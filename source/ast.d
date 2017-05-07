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
module ast;

import std.algorithm : any, canFind, joiner, map;
import std.bigint : BigInt;
import std.conv : to;
import std.range : chain, InputRange, inputRangeObject;
import std.traits : isArray, isAssociativeArray;
import std.variant : Algebraic;

import error : error, Position;

template dispatch(alias fun, Types...) {
	auto dispatch(T...)(auto ref T args) {
		foreach (Type; Types) {
			if (auto sub = cast(Type) args[0]) {
				return fun(sub, args[1 .. $]);
			}
		}
		assert(0, args[0].to!string);
	}
}

alias Index = Algebraic!(BigInt, string);

Node[] childrenRange() {
	return [];
}

auto childrenRange(T)(ref T node) if (is(T : Node)) {
	return node is null ? childrenRange : (cast(Node*)&node)[0 .. 1];
}

auto childrenRange(T)(ref T array) if (isArray!T) {
	return array.map!(.childrenRange).joiner;
}

auto childrenRange(T)(ref T array) if (isAssociativeArray!T) {
	return array.byValue.map!(.childrenRange).joiner;
}

auto childrenRange(T...)(ref T args) if (T.length > 1) {
	return childrenRange(args[0]).chain(childrenRange(args[1 .. $]));
}

alias Children = InputRange!Node;

mixin template autoChildren(T...) {
	override Children children() {
		auto range = childrenRange(T);
		return inputRangeObject(range);
	}
}

interface SearchContext {
	Var searchVar(string name, string[] namespace, ref Trace); //trace is an out variable with is by default the current trace
	Type searchType(string name, string[] namespace, ref Trace);
	//for some types(scopes) looping over children changes the searchcontext
	void pass(Node child);
}

template SearchContextImpl(alias imports, alias staticimports, alias aliases) {
	Var searchVar(string name, string[] namespace, ref Trace trace) {
		if (namespace is null) {
			foreach (mod; imports) {
				if (name in mod.vars) {
					trace = Trace(mod, null);
					return mod.vars[name];
				}
			}
		} else {
			if (namespace in staticimports) {
				auto mods = staticimports[namespace];
				foreach (mod; mods) {
					if (name in mod.vars) {
						trace = Trace(mod, null);
						return mod.vars[name];
					}
				}
			}
		}
		return null;
	}

	Type searchType(string name, string[] namespace, ref Trace trace) {
		if (namespace is null) {
			auto type = name in aliases;
			if (type) {
				return *type;
			}
			foreach (mod; imports) {
				if (name in mod.aliases) {
					trace = Trace(mod, null);
					return mod.aliases[name];
				}
			}
		} else {
			if (namespace in staticimports) {
				auto mods = staticimports[namespace];
				foreach (mod; mods) {
					if (name in mod.aliases) {
						trace = Trace(mod, null);
						return mod.aliases[name];
					}
				}
			}
		}
		return null;
	}
}

struct Trace {
	Node node;
	SearchContext context;
	Trace* upper;

	this(Node node, Trace* upper) {
		this.node = node;
		this.context = node.context();
		this.upper = upper;
	}

	Var searchVar(string name, string[] namespace) {
		Trace trace;
		return searchVar(name, namespace, trace);
	}

	Var searchVar(string name, string[] namespace, ref Trace trace) {
		trace = this;
		if (context) {
			if (auto result = context.searchVar(name, namespace, trace)) {
				return result;
			}
		}
		if (upper) {
			return upper.searchVar(name, namespace, trace);
		} else {
			return null;
		}
	}

	Type searchType(string name, string[] namespace) {
		Trace trace;
		return searchType(name, namespace, trace);
	}

	Type searchType(string name, string[] namespace, ref Trace trace) {
		trace = this;
		if (context) {
			if (auto result = context.searchType(name, namespace, trace)) {
				return result;
			}
		}
		if (upper) {
			return upper.searchType(name, namespace, trace);
		} else {
			return null;
		}
	}
}

struct TraceRange {
	Trace* current;
	bool empty() {
		return current is null;
	}

	ref Trace front() {
		return *current;
	}

	void popFront() {
		current = current.upper;
	}

	auto save() {
		return this;
	}
}

auto range(Trace* trace) {
	return TraceRange(trace);
}

bool cycle(Node node, Trace* trace) {
	return trace.range.any!(a => a.node == node);
}

abstract class Node { //base class for all ast nodes
	Position pos;
	Children children();
	SearchContext context() {
		return null;
	}
}

abstract class Type : Node {
	@property Type actual() {
		return this;
	}

	Bool isBool() {
		return cast(Bool) actual;
	}

	Char isChar() {
		return cast(Char) actual;
	}

	Int isInt() {
		return cast(Int) actual;
	}

	UInt isUInt() {
		return cast(UInt) actual;
	}

	Struct isStruct() {
		return cast(Struct) actual;
	}

	Pointer isPointer() {
		return cast(Pointer) actual;
	}

	Array isArray() {
		return cast(Array) actual;
	}

	Function isFunction() {
		return cast(Function) actual;
	}
}

class Bool : Type {
	mixin autoChildren!();
}

class Char : Type {
	mixin autoChildren!();
}

class Int : Type {
	uint size;
	this(uint _) {
		size = _;
	}

	mixin autoChildren!();
}

class UInt : Type {
	uint size;
	this(uint _) {
		size = _;
	}

	mixin autoChildren!();
}

class Struct : Type {
	Type[] types;
	size_t[string] names;

	mixin autoChildren!types;
}

class Pointer : Type {
	Type type;
	mixin autoChildren!type;
}

class Array : Type {
	Type type;
	mixin autoChildren!type;
}

class Function : Type {
	Type ret;
	Type arg;
	bool ispure;
	mixin autoChildren!(ret, arg);
}

abstract class IndirectType : Type {
	Type actual_;
override:
	@property Type actual() {
		return actual_.actual;
	}
}

class UnknownType : IndirectType {
	string name;
	string[] namespace;
	mixin autoChildren!();
}

//for position dependant statements
abstract class Statement : Node {
	bool ispure;
}

abstract class Var : Statement {
	string name;
	bool manifest;
	bool heap; //has the address of the variable been taken,does not apply to closures
	@property abstract ref Type getType();
}

class ModuleVar : Var {
	Value def;
	bool process;
	mixin autoChildren!def;
override:
	@property ref Type getType() {
		return def.type;
	}
}

class Module : Node, SearchContext {
	Type[string] aliases;
	Module[] imports;
	Module[][string[]] staticimports;
	ModuleVar[string] vars;
	string[] namespace;

override:
	SearchContext context() {
		return this;
	}

	Var searchVar(string name, string[] namespace, ref Trace trace) {
		if (namespace is null && name in vars) {
			return vars[name];
		}
		return SearchContextImpl!(imports, staticimports, aliases).searchVar(name,
				namespace, trace);
	}

	Type searchType(string name, string[] namespace, ref Trace trace) {
		return SearchContextImpl!(imports, staticimports, aliases).searchType(name,
				namespace, trace);
	}

	void pass(Node) {
	}

	mixin autoChildren!(aliases, vars);
}

abstract class Value : Statement {
	Type type;
	bool lvalue;
}

class IntLit : Value {
	BigInt value;
	bool usigned;
	mixin autoChildren!();
}

class CharLit : Value {
	dchar value;
	mixin autoChildren!();
}

class BoolLit : Value {
	bool yes;
	mixin autoChildren!();
}

class StructLit : Value {
	Value[] values;
	size_t[string] names;
	mixin autoChildren!values;
}

class Variable : Value {
	string name;
	string[] namespace;
	mixin autoChildren!();
}

class If : Value {
	Value cond;
	Value yes;
	Value no;
	mixin autoChildren!(cond, yes, no);
}

class While : Value {
	Value cond;
	Value state;
	mixin autoChildren!(cond, state);
}

class New : Value {
	Value value;
	mixin autoChildren!value;
}

class NewArray : Value {
	Value length;
	Value value;
	mixin autoChildren!(length, value);
}

class Cast : Value {
	Value value;
	Type wanted;
	mixin autoChildren!(value, wanted);
}

class Dot : Value {
	Value value;
	Index index;
	mixin autoChildren!value;
}

class ArrayIndex : Value {
	Value array;
	Value index;
	mixin autoChildren!(array, index);
}

class FCall : Value {
	Value fptr;
	Value arg;
	mixin autoChildren!(fptr, arg);
}

class Slice : Value {
	Value array;
	Value left;
	Value right;
	mixin autoChildren!(array, left, right);
}

class Binary(string T) : Value 
		if (["*", "/", "%", "+", "-", "~", "==", "!=",
			"<=", ">=", "<", ">", "&&", "||", "="].canFind(T)) {
	Value left;
	Value right;
	mixin autoChildren!(left, right);
}

class Prefix(string T) : Value if (["+", "-", "*", "/", "&", "!"].canFind(T)) {
	Value value;
	mixin autoChildren!value;
}

class ScopeVar : Var {
	Value def;
	mixin autoChildren!def;
override:
	@property ref Type getType() {
		return def.type;
	}
}

class Scope : Value {
	Type[string] aliases;
	Module[] imports;
	Module[][string[]] staticimports;
	Statement[] states;
	Value last;

	static class ScopeContext : SearchContext {
		Scope that;
		ScopeVar[string] vars;

		this(Scope that) {
			this.that = that;
		}

		Var searchVar(string name, string[] namespace, ref Trace trace) {
			if (namespace is null && name in vars) {
				return vars[name];
			}
			auto imports = that.imports;
			auto staticimports = that.staticimports;
			auto aliases = that.aliases;
			return SearchContextImpl!(imports, staticimports, aliases).searchVar(name,
					namespace, trace);
		}

		Type searchType(string name, string[] namespace, ref Trace trace) {
			auto imports = that.imports;
			auto staticimports = that.staticimports;
			auto aliases = that.aliases;
			return SearchContextImpl!(imports, staticimports, aliases).searchType(name,
					namespace, trace);
		}

		void pass(Node node) {
			if (auto var = cast(ScopeVar) node) {
				vars[var.name] = var;
			}
		}
	}

override:
	SearchContext context() {
		return new ScopeContext(this);
	}

	mixin autoChildren!(aliases, states);
}

class FuncLitVar : Var {
	Type ty;
	mixin autoChildren!ty;
	override ref Type getType() {
		return ty;
	}
}

class FuncLit : Value, SearchContext {
	FuncLitVar fvar;
	Value text;
	Type explict_return; //maybe null

override:

	SearchContext context() {
		return this;
	}

	Var searchVar(string name, string[] namespace, ref Trace) {
		if (namespace is null && fvar.name == name) {
			return fvar;
		}
		return null;
	}

	Type searchType(string name, string[] namespace, ref Trace) {
		return null;
	}

	void pass(Node) {
	}

	mixin autoChildren!(fvar, text, explict_return);
}

class StringLit : Value {
	string str;
	mixin autoChildren!();
}

class ArrayLit : Value {
	Value[] values;
	mixin autoChildren!values;
}

class ExternJS : Value {
	string external;
	mixin autoChildren!type;
}
