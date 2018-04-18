import std.conv;

template dispatch(alias fun, Types...) {
	auto dispatch(Base, T...)(Base base, auto ref T args) {
		foreach (Type; Types) {
			if (cast(Type) base) {
				return fun(cast(Type) base, args);
			}
		}
		assert(0, base.to!string);
	}
}

T castTo(T, Base)(Base node) {
	return cast(T) node;
}

import core.runtime;
import core.stdc.stdlib;
import std.conv;
import std.stdio;

struct Position { //used for token position in a file
	string file_name;
	uint line;
	string file; //ref to file
	size_t indexs; //file index start
	size_t indexe; //file index end
	auto join(Position other) {
		assert(file_name == other.file_name, file_name ~ " " ~ other.file_name);
		assert(file.ptr == other.file.ptr);
		return Position(file_name, line, file, indexs, other.indexs);
	}

	string toString() {
		return file[indexs .. indexe];
	}
}

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
	stderr.writeln("Error: " ~ message);
	stderr.writeln(prettyPrint(pos));
	Runtime.terminate();
	exit(1);
}

void error(string message) {
	stderr.writeln("Error: " ~ message);
	Runtime.terminate();
	exit(1);
}

void warn(string message, Position pos) {
	stderr.writeln("Warning: " ~ message);
	writeln(prettyPrint(pos));
}
