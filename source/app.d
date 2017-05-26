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

import error : error;
import parser;
import lexer;
import semantic;
import codegen;
import ast;
import jsast;

MmFile[] maps;

void readFiles(string[][] imports, string[][] files, out Module[string[]] wanted,
		out Module[string[]] all) {
	string openImport(string[] mod) {
		auto builder = mod.take(mod.length - 1).chain(only(mod[$ - 1] ~ ".typi"));
		foreach (imp; imports) {
			try {
				auto map = new MmFile(buildPath(chain(imp, builder.save)));
				maps ~= map;
				return cast(string) map[];
			}
			catch (Exception e) {

			}
		}
		error("Unable to open file " ~ buildPath(builder.save));
		return null;
	}

	Module loadModule(string[] imp) {
		auto m = imp in all;
		if (m) {
			return *m;
		}
		auto parser = Parser(Lexer(imp.join("::").to!string, openImport(imp)), &loadModule);
		auto mod = parser.parseModule(imp);
		all[imp.idup] = mod;
		return mod;
	}

	foreach (f; files) {
		wanted[f.idup] = loadModule(f);
	}
}

enum Help = `typi {optional arguments} [files to compile]
--Generate-All|-a : generate code for all imported files, default is to only generate code for command line files
--Add-Search-Dir|-I : add search directory for imports
--Output|-o : output file, - is the default and means stdout
--Namespace|-n : namespace to compile the javascript to default is global
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
	string[] searchDirs = ["."];
	string outputFile = "-";
	string jsname = "";
	void opt(ref string[] s) {
		getopt(s, "Generate-All|a", &genAll, "Add-Search-Dir|I", &searchDirs,
				"Output|o", &outputFile, "Namespace|n", &jsname);
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

	Module[string[]] wanted;
	Module[string[]] all;

	string[][] modnames;
	foreach (file; args) {
		if (!(file.endsWith(".typi") || file.endsWith(".js"))) {
			writeln(file, " is not a typi file");
			return;
		}
		if (file.endsWith(".typi")) {
			modnames ~= file[0 .. $ - ".typi".length].split(dirSeparator);
		}
	}
	auto importPaths = searchDirs.split(dirSeparator).filter!(a => a.length)
		.map!(a => a.array).array;
	readFiles(importPaths, modnames, wanted, all);
	all.each!(a => processModule(a));
	File output;
	if (outputFile == "-") {
		output = stdin;
	} else {
		output = File(outputFile, "w");
	}
	auto writer = &output.write!(const(char)[]);
	if (genAll) {
		foreach (mod; all.values) {
			generateJSModule(mod, jsname).each!((a) {
				a.toStateString(writer, 0);
				output.writeln;
			});
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
				generateJSModule(wanted[file[0 .. $ - ".typi".length].split(dirSeparator)
						.array], jsname).each!((a) {
					a.toStateString(writer, 0);
					output.writeln;
				});
			} else {
				File(file, "r").byChunk(4096).map!(a => cast(const(char)[]) a).copy(writer);
			}
		}
	}
	output.close;
}
