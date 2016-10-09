/+Copyright (C) 2015  Freddy Angel Cubas "Superstar64"

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, version 3 of the License.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
+/
import std.stdio;
import parser;
import lexer;
import semantic;
import codegen;
import ast;
import std.getopt;
import std.array;
import std.path;
import std.file;
import std.process;

enum Help = `typi {optional arguments} [files to compile]
--Generate-All|-a : generate code for all imported files, default is to only generate code for command line files
--Add-Search-Dir|-I : add search directory for imports
--Output|-o : output file, - is the default and means stdout
--Namespace|-n : namespace to compile the javascript to default is global
The TYPI_CONFIG enviroment Variable is looked at for a config file(extra arguments sperated by lines)
Any .js files in [files to compile] are interpeted as runtime files and will be include into the output

Copyright (C) 2015  Freddy Angel Cubas "Superstar64"
This software has no warrenty.
You may distrubute this software under the General Public Licenese Version 3
`;

void main(string[] args) {
	args = args[1 .. $];
	if (args.length == 0) {
		writeln(Help);
		return;
	}
	bool genAll;
	string[] searchDirs = ["."];
	string output = "-";
	string jsname = "";
	void opt(ref string[] s) {
		getopt(s, "Generate-All|a", &genAll, "Add-Search-Dir|I", &searchDirs,
			"Output|o", &output, "Namespace|n", &jsname);
	}

	string configFile = environment.get("TYPI_CONFIG");
	if (configFile !is null) {
		auto file = cast(string) read(configFile);
		auto lines = file.split("\n");
		opt(lines);
		args ~= lines;
	}

	opt(args);
	Loader l;
	foreach (ref f; searchDirs) {
		f = replace(f, "::", dirSeparator);
	}
	l.importPaths = searchDirs;

	Module[string[]] wanted;
	Module[string[]] all;

	Module[string[]] actual;
	string[][] modnames;
	string[] runtime;
	foreach (f; args) {
		if ((f.length < ".typi".length || f[$ - ".typi".length .. $] != ".typi")
				&& (f.length < ".js".length || f[$ - ".js".length .. $] != ".js")) {
			writeln(f, " is not a typi file");
			return;
		}
		if (f[$ - ".js".length .. $] == ".js") {
			runtime ~= f;
		} else {
			modnames ~= f[0 .. $ - ".typi".length].split(dirSeparator);
		}
	}
	readFiles(l, modnames, wanted, all);
	processModules(all.values);
	if (genAll) {
		actual = all;
	} else {
		actual = wanted;
	}
	string prefix;
	foreach (f; runtime) {
		prefix ~= cast(string) read(f);
	}
	auto str = prefix ~ genJS(actual.values, jsname);
	if (output == "-") {
		writeln(str);
	} else {
		std.file.write(output, str);
	}
}
