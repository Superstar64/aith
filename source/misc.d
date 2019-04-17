import std.conv;
import std.traits;
import std.algorithm;
import std.typecons;
import std.array;

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

template castTo(T) {
	T castTo(Base)(Base node) {
		static if (is(isImplicitlyConvertible!(Base, T))) {
			static assert(0,
					T.stringof ~ " is a base class of " ~ Base.stringof ~ "use convert instead");
		}
		return cast(T) node;
	}
}

template convert(T) {
	T convert(Base)(Base node) {
		return node;
	}
}

template castToPermissive(T) {
	T castToPermissive(Base)(Base node) {
		return cast(T) node;
	}
}

template Pack(T...) {
	alias expand = T;
}

auto tupleEnumerateImpl()(int index) {
	return tuple();
}

auto tupleEnumerateImpl(H, T...)(int index, H head, T tail) {
	return tuple(tuple(index, head), tupleEnumerateImpl(index + 1, tail).expand);
}

auto tupleEnumerateImpl(Tuple...)(Tuple t) {
	return tupleEnumerateImpl(0, t);
}

auto tupleMap(alias fun, int[] pass = [])() {
	return tuple();
}

auto tupleMap(alias fun, int[] pass = [], H, T...)(H head, T tail) {
	static if (pass.any!"a == 0") {
		return tuple(head, tupleMap!(fun, map!(a => a - 1)(pass).array)(tail).expand);
	} else {
		return tuple(fun(head), tupleMap!(fun, map!(a => a - 1)(pass).array)(tail).expand);
	}
}

auto tupleCall(alias fun)() {
	return tuple();
}

auto tupleCall(alias fun, H, T...)(H head, T tail) {
	return tuple(fun.expand[0](head), tupleCall!(Pack!(fun.expand[1 .. $]))(tail).expand);
}

auto tupleFold(alias fun, int[] pass = [], Seed)(Seed seed) {
	return seed;
}

auto tupleFold(alias fun, int[] pass = [], Seed, H, T...)(Seed seed, H head, T tail) {
	static if (pass.any!"a == 0") {
		return tupleFold!(fun, map!(a => a - 1)(pass).array)(seed, tail);
	} else {
		auto next = fun(seed, head);
		return tupleFold!(fun, map!(a => a - 1)(pass).array)(next, tail);
	}
}

Tuple!()[T] arrayToSet(T)(T[] data) {
	Tuple!()[T] result;
	foreach (d; data) {
		result[d] = tuple();
	}
	return result;
}

bool isSubSet(T)(Tuple!()[T] smaller, Tuple!()[T] bigger) {
	foreach (key; smaller.byKey) {
		if (!(key in bigger)) {
			return false;
		}
	}
	return true;
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

void check(T)(T expression, string message, Position position,
		string file = __FILE__, int line = __LINE__) {
	if (!expression) {
		error(message, position, file, line);
	}
}
