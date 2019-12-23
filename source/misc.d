import std.conv;
import std.traits;
import std.algorithm;
import std.typecons;
import std.array;
import core.runtime;
import core.stdc.stdlib;
import std.stdio;
import std.meta;
import std.format;
import std.range;
import std.bigint;

import jsast : Json, JsonInt, JsonBool, JsonChar, JsonArray, JsonObject;

class Lazy(T) {
	T delegate() callback;
	struct Value {
		T val;
	}

	Value* value;

	this(T delegate() callback) {
		this.callback = callback;
	}

	T get() {
		if (value is null) {
			auto v = callback();
			value = new Value(v);
		}
		return value.val;
	}

	void eval() {
		get();
	}
}

Lazy!T defer(T)(T delegate() callback) {
	return new Lazy!T(callback);
}

interface Jsonable {
	Json jsonify();
}

Json jsonify(int x) {
	return new JsonInt(x);
}

Json jsonify(BigInt x) {
	return new JsonInt(x);
}

Json jsonify(bool x) {
	return new JsonBool(x);
}

Json jsonify(string x) {
	return new JsonChar(x);
}

Json jsonify(T)(T[] list) {
	return new JsonArray(list.map!jsonify.array);
}

Json jsonify(V)(V[string] map) {
	JsonObject base = new JsonObject;
	foreach (name; map.byKey) {
		base.fields ~= tuple(name, map[name].jsonify);
	}
	return base;
}

Json jsonify(T)(Lazy!T x) {
	return x.get.jsonify;
}

Json jsonify(Jsonable dispatch) {
	return dispatch.jsonify();
}

template GetMember(T) {
	alias GetMember(string name) = AliasSeq!(__traits(getMember, T, name));
}

alias PropertyNameTuple(T) = __traits(derivedMembers, T);

alias PropertyTypeTuple(T) = staticMap!(ReturnType, staticMap!(GetMember!T,
		PropertyNameTuple!T));

mixin template Getters(T) {
	import std.format;
	import std.traits;

	static foreach (field; PropertyNameTuple!T) {
		mixin(q{ private ReturnType!(__traits(getMember,T,field)) _%s;}.format(field));
		mixin(q{ override %s ReturnType!(__traits(getMember,T,field)) %s(){
				return _%s;
			}}.format(
				functionAttributes!(__traits(getMember,
				T, field)) & FunctionAttribute.ref_ ? "ref" : "", field, field));
	}
	this(PropertyTypeTuple!T arguments) {
		static foreach (c, field; PropertyNameTuple!T) {
			mixin(q{this._%s = arguments[c];}.format(field));
		}
	}

	auto properties()() {
		mixin(q{return .tuple(} ~ [PropertyNameTuple!T].map!(a => "_" ~ a ~ ",").joiner.array
				~ q{);});
	}

	import jsast : Json;

	Json jsonifyImpl()() {
		import jsast;
		static import std.typecons;
		static import std.conv;
		static import misc;

		JsonObject base = new JsonObject;
		base.fields ~= std.typecons.tuple("_name", misc.jsonify(T.stringof));
		//base.fields ~= std.typecons.tuple("_address", misc.jsonify(std.conv.to!string(cast(void*)(this))) );
		static foreach (c, field; PropertyNameTuple!T) {
			mixin(q{base.fields ~= std.typecons.tuple("%s",this.%s.jsonify);}.format(field, field));
		}
		return base;
	}
}

class DefaultImpl(T) : T {
	this() {
	}

	mixin Getters!T;
}

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

template convert(T) {
	T convert(Base)(Base node) {
		return node;
	}
}

template Pack(T...) {
	alias expand = T;
}

Tuple!()[T] arrayToSet(T)(T[] data) {
	Tuple!()[T] result;
	foreach (d; data) {
		result[d] = tuple();
	}
	return result;
}

T[] emptyArray(T)() {
	return null;
}

Tuple!()[T] emptySet(T)() {
	return null;
}

V[K] emptyMap(K, V)() {
	return null;
}

Tuple!()[T] singleSet(T)(T data) {
	return arrayToSet([data]);
}

Tuple!()[T] mergeSets(T)(Tuple!()[T] left, Tuple!()[T] right) {
	return arrayToSet(left.keys ~ right.keys);
}

auto mergeSets(H, T...)(H first, H second, T tail) if (tail.length > 0) {
	return mergeSets(mergeSets(first, second), tail);
}

bool isSubSet(T)(Tuple!()[T] smaller, Tuple!()[T] bigger) {
	foreach (key; smaller.byKey) {
		if (!(key in bigger)) {
			return false;
		}
	}
	return true;
}

K[V] mergeMaps(K, V)(K[V] left, K[V] right) {
	K[V] result;
	foreach (k; left.byKey) {
		result[k] = left[k];
	}
	foreach (k; right.byKey) {
		result[k] = right[k];
	}
	return result;
}

auto mergeMaps(H, T...)(H first, H second, T tail) if (tail.length > 0) {
	return mergeMaps(mergeMaps(first, second), tail);
}

struct Source {
	string fileName;
	string file;
}

struct Section {
	uint lineStart;
	uint lineEnd;
	size_t start;
	size_t end;
}

struct Position {
	Source source;
	Section section;
}

Position join(Position left, Position right) {
	assert(left.source == right.source);
	return Position(left.source, Section(left.section.lineStart,
			right.section.lineEnd, left.section.start, right.section.end));
}

//todo rework pretty printing
string prettyPrint(Position pos, string colorstart = "\x1b[31m", string colorend = "\x1b[0m") {
	string res;
	res ~= "in file:" ~ pos.source.fileName ~ " at line:" ~ pos.section.lineStart.to!string ~ "\n";
	res ~= colorstart ~ pos.source.file[pos.section.start .. pos.section.end] ~ colorend;
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
