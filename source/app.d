/+
	Copyright (C) 2020  Freddy Angel Cubas "Superstar64"
	This file is part of Aith.

	Aith is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation version 3 of the License.

	Aith is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with Aith.  If not, see <http://www.gnu.org/licenses/>.
+/
module app;

import std.algorithm;
import std.array;
import std.conv;
import std.getopt;
import std.process;
import std.path;
import std.mmfile;
import std.range;
import std.stdio;
import std.file : exists, isDir;
import core.stdc.stdlib : exit;
import std.typecons;

import misc.misc;
import misc.container;

import Lexer = lexer;
import Parser = parser.ast;
import Semantic = semantic.ast;
import JsAst = jsast;

import ParserEval = parser.parser;
import SemanticEval = semantic.semantic;
import CodegenEval = codegen.codegen;

__gshared {
	string[] searchDirs = ["."];
	MmFile[] maps;

	OwnerDictonary!(Semantic.SymbolId, Semantic.SymbolValue) knownSymbols;
	OwnerDictonary!(Parser.ModuleBinding, Semantic.ModuleDefinition) knownBindings;

	OwnerDictonary!(Semantic.PredicateId, Semantic.TypeMatch[]) knownPredicateMatches;

	OwnerDictonary!(string, Parser.Module) parserModules;
	OwnerDictonary!(Parser.Module, Semantic.Module) semanticModules;
	Semantic.Module builtin;
}

T freshId(T)() {
	static __gshared size_t global = 0;
	return T(global++);
}

Parser.Module readParserModule(string name) {
	if (name in parserModules) {
		return parserModules[name];
	}
	foreach (dir; searchDirs) {
		auto fileName = dir ~ dirSeparator ~ name;
		if (exists(fileName)) {
			auto file = new MmFile(fileName);
			maps ~= file;
			auto buffer = file[].castTo!string;
			auto lexer = Lexer.Lexer(fileName, buffer);
			auto result = ParserEval.parseModule(lexer);
			parserModules.insert(name, result);
			return result;
		}
	}
	stderr.writeln("can't find module " ~ name);
	exit(1);
	assert(0);
}

Semantic.Module readSemanticModule(Parser.Module parserModule) {
	if (parserModule in semanticModules) {
		return semanticModules[parserModule];
	}
	auto result = SemanticEval.createModule(parserModule, builtin);
	semanticModules.insert(parserModule, result);
	return result;
}

auto stringifyVariable(Semantic.TypeVariableId var, Semantic.TypeRequirement requirement) {
	import semantic.astimpl : make;

	string result = "v" ~ var.raw.to!string;
	if (requirement.predicates.length > 0) {
		result ~= " extends ";
		result ~= requirement.predicates.byValue.map!(a => a.to!string).joiner(" & ").to!string;
	}
	return result;
}

enum Help = `aith {optional arguments} [files to compile]
--Generate-All|-a : generate code for all imported files, default is to only generate code for command line files
--Add-Search-Dir|-I : add search directory for imports
--Output|-o : output file, - is the default and means stdout
--printTypes : don't generate code, print types of all module declarations
--builtin : signify builtin module
The TYPI_CONFIG enviroment Variable is looked at for a config file(extra arguments sperated by lines)
Any .js files in [files to compile] are interpeted as runtime files and will be included after the output

This software has no warrenty.
You may distrubute this software under the General Public Licenese Version 3
`;

void main(string[] args) {

	if (args.length == 1) {
		writeln(Help);
		return;
	}
	bool genAll;
	bool printTypes;
	string outputFile = "-";
	string builtinFile;
	void opt(ref string[] s) {
		getopt(s, "Generate-All|a", &genAll, "Add-Search-Dir|I", &searchDirs, "Output|o", &outputFile, "printTypes", &printTypes, "builtin", &builtinFile);
	}

	string configFile = environment.get("TYPI_CONFIG");
	if (configFile !is null) {
		auto file = File(configFile, "r");
		auto lines = chain(only(args[0]), file.byLineCopy).array;
		opt(lines);
		args ~= lines[1 .. $];
	}
	opt(args);
	args = args[1 .. $];
	foreach (dir; searchDirs) {
		if (!exists(dir)) {
			stderr.writeln(dir ~ "does not exist");
			exit(1);
		}
		if (!isDir(dir)) {
			stderr.writeln(dir ~ "is not a directory");
			exit(1);
		}
	}

	string[] modFiles;
	foreach (file; args) {
		if (!(file.endsWith(".aith") || file.endsWith(".js"))) {
			writeln(file, " is not a aith file");
			return;
		}
		if (file.endsWith(".aith")) {
			modFiles ~= file;
		}
	}

	if (builtinFile != "") {
		builtin = builtinFile.readParserModule.readSemanticModule;
	}

	Semantic.Module[string] wanted;
	foreach (file; modFiles) {
		wanted[file] = file.readParserModule.readSemanticModule;
	}
	wanted.byValue.each!(a => SemanticEval.validateModule(a));
	File output;
	if (outputFile == "-") {
		output = stdout;
	} else {
		output = File(outputFile, "w");
	}
	auto writer = &output.write!(const(char)[]);
	if (printTypes) {
		foreach (file; args) {
			if (file.endsWith(".aith")) {
				auto want = wanted[file];
				auto modulename = file[0 .. $ - ".aith".length];
				writeln(modulename, "{");
				foreach (variable; want.orderedAliases) {
					auto name = want.aliases.range.find!(a => a.value is variable).front.key;
					if (auto expression = Semantic.get(variable).matrix.castTo!(Semantic.Term)) {
						string forall = "";
						auto prefix = Semantic.get(variable).typePrefix;
						if (prefix.length > 0) {
							forall ~= "<";
							forall ~= prefix.range.map!(a => stringifyVariable(a.key, a.value)).joiner(", ").to!string;
							forall ~= "> ";
						}
						writeln("\t", name, " : ", forall, expression.type.to!string);
						writeln("\t", name, " @ ", expression.type.type.to!string);
					}
				}
				writeln("}");
			}
		}
	} else if (genAll) {
		foreach (mod; semanticModules.byValue) {
			CodegenEval.generateJsModule(mod).toStateString(writer, 0, new JsAst.JsContext());
			output.writeln;
		}
		foreach (file; args) {
			if (file.endsWith(".js")) {
				File(file, "r").byChunk(4096).map!(castTo!(const(char)[])).copy(writer);
			}
		}
	} else {
		foreach (file; args) {
			if (file.endsWith(".aith")) {
				auto want = wanted[file];
				//writeln(want.jsonify.to!string);
				CodegenEval.generateJsModule(want).toStateString(writer, 0, new JsAst.JsContext());
			} else {
				File(file, "r").byChunk(4096).map!(castTo!(const(char)[])).copy(writer);
			}
		}
	}
	output.close;
}
