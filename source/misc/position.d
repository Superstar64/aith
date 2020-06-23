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

module misc.position;

import std.conv;
import core.runtime;
import std.stdio;
import core.stdc.stdlib;

struct Source {
	string fileName;
	string file;
}

struct Line {
	size_t start;
	size_t end;
}

struct Section {
	uint line;
	size_t start;
	size_t end;
	Line startLine;
	Line endLine;
}

struct Position {
	Source source;
	Section section;
}

Position join(Position left, Position right) {
	assert(left.source == right.source);
	auto section = Section(left.section.line, left.section.start, right.section.start, left.section.startLine, right.section.startLine);
	return Position(left.source, section);
}

//todo rework pretty printing
string prettyPrint(Position pos, string colorstart = "\x1b[31m", string colorend = "\x1b[0m") {
	string res;
	res ~= "in file:" ~ pos.source.fileName ~ " at line:" ~ pos.section.line.to!string ~ "\n";
	res ~= pos.source.file[pos.section.startLine.start .. pos.section.start];
	res ~= colorstart ~ pos.source.file[pos.section.start .. pos.section.end] ~ colorend;
	res ~= pos.source.file[pos.section.end .. pos.section.endLine.end];
	return res;
}

void error(string message, Position pos, string file = __FILE__, int line = __LINE__) {
	stderr.writeln("Error: " ~ message);
	stderr.writeln(prettyPrint(pos));
	stderr.writeln("Compiler:" ~ file ~ " at " ~ line.to!string);
	Runtime.terminate();
	exit(1);
}

void error(string message, string file = __FILE__, int line = __LINE__) {
	stderr.writeln("Error: " ~ message);
	stderr.writeln("Compiler:" ~ file ~ " at " ~ line.to!string);
	Runtime.terminate();
	exit(1);
}

void warn(string message, Position pos) {
	stderr.writeln("Warning: " ~ message);
	writeln(prettyPrint(pos));
}

void check(T)(T expression, string message, Position position, string file = __FILE__, int line = __LINE__) {
	if (!expression) {
		error(message, position, file, line);
	}
}
