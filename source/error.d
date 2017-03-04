/+
	This file is part of Typi.

	Typi is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	Typi is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with Typi.  If not, see <http://www.gnu.org/licenses/>.
+/
module error;
import core.runtime : Runtime;
import core.stdc.stdlib : exit;
import std.stdio : write, writeln;
import lexer;
import std.conv : to;

string prettyPrint(Position pos, string colorstart = "\x1b[31m", string colorend = "\x1b[0m") {
	string res;
	res ~= "in file:" ~ pos.file_name ~ " at line:" ~ pos.line.to!string ~ "\n";
	size_t lower = pos.indexs;
	size_t upper = pos.indexe;

	if (lower == pos.file.length) {
		res ~= "at Eof";
		return res;
	}

	if (lower != 0) {
		while (true) {
			if (pos.file[lower] == '\n') {
				break;
			}
			lower--;
			if (lower == 0) {
				break;
			}
		}
		lower++;
	}
	while (upper != pos.file.length) {
		if (pos.file[upper] == '\n') {
			break;
		}
		upper++;
	}

	res ~= pos.file[lower .. pos.indexs];
	res ~= colorstart ~ pos.file[pos.indexs .. pos.indexe] ~ colorend;
	res ~= pos.file[pos.indexe .. upper];
	return res;
}

void error(string message, Position pos) {
	writeln("Error: " ~ message);
	writeln(prettyPrint(pos));
	Runtime.terminate();
	exit(1);
}

void error(string message) {
	writeln("Error: " ~ message);
	Runtime.terminate();
	exit(1);
}

void warn(string message, Position pos) { //todo count warnings and add easter eggs
	writeln("Warning: " ~ message);
	writeln(prettyPrint(pos));
}
