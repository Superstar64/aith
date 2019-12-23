/+
	Copyright (C) 2015-2017  Freddy Angel Cubas "Superstar64"
	This file is part of Typi.

	Typi is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation version 3 of the License.

	Typi is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with Typi.  If not, see <http://www.gnu.org/licenses/>.
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

import misc;
import parser.parser;
import lexer;
import semantic.semantic;
import codegen.codegen;

static import Parser = parser.ast;
import semantic.ast;
import jsast;

Module[string] all;
string[] searchDirs = ["."];
MmFile[] maps;

Module findAndReadModule(string name) {
	if (name in all) {
		return all[name];
	}
	foreach (dir; searchDirs) {
		if (exists(dir ~ dirSeparator ~ name)) {
			return readModule(dir ~ dirSeparator ~ name);
		}
	}
	stderr.writeln("can't find module " ~ name);
	exit(1);
	assert(0);
}

Module readModule(string name) {
	auto parserMod = new Parser.Module();
	auto map = new MmFile(name);
	maps ~= map;
	auto buffer = cast(string) map[];
	auto lexer = Lexer(name, buffer);
	parseModule(lexer, parserMod);
	auto semanticMod = lazyCreateModule(parserMod);
	all[name] = semanticMod;
	return semanticMod;
}

void readFiles(string[] fileNames, out Module[string] wanted) {
	foreach (name; fileNames) {
		if (!exists(name)) {
			stderr.writeln(name ~ " doesn't exist");
			exit(1);
		}
		wanted[name] = readModule(name);
	}
}

enum Help = `typi {optional arguments} [files to compile]
--Generate-All|-a : generate code for all imported files, default is to only generate code for command line files
--Add-Search-Dir|-I : add search directory for imports
--Output|-o : output file, - is the default and means stdout
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

	string outputFile = "-";
	void opt(ref string[] s) {
		getopt(s, "Generate-All|a", &genAll, "Add-Search-Dir|I", &searchDirs,
				"Output|o", &outputFile);
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
		if (!(file.endsWith(".typi") || file.endsWith(".js"))) {
			writeln(file, " is not a typi file");
			return;
		}
		if (file.endsWith(".typi")) {
			modFiles ~= file;
		}
	}

	Module[string] wanted;
	readFiles(modFiles, wanted);
	all.each!(a => processModule(a));
	File output;
	if (outputFile == "-") {
		output = stdout;
	} else {
		output = File(outputFile, "w");
	}
	auto writer = &output.write!(const(char)[]);
	if (genAll) {
		foreach (mod; all.values) {
			generateJsModule(mod.toRuntime).toStateString(writer, 0, JsContext());
			output.writeln;
		}
		foreach (file; args) {
			if (file.endsWith(".js")) {
				File(file, "r").byChunk(4096).map!(a => cast(const(char)[]) a).copy(writer);
			}
		}
	} else {
		foreach (file; args) {
			if (file.endsWith(".typi")) {
				auto want = wanted[file].toRuntime;
				//writeln(want.jsonify.to!string);
				generateJsModule(want).toStateString(writer, 0, JsContext());
			} else {
				File(file, "r").byChunk(4096).map!(a => cast(const(char)[]) a).copy(writer);
			}
		}
	}
	output.close;
}
