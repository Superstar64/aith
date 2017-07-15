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
	Var search(string name, ref Trace); //trace is an out variable with is by default the current trace
	//for some types(scopes) looping over children changes the searchcontext
	void pass(Node child);
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

	Var search(string name) {
		Trace trace;
		return search(name, trace);
	}

	Var search(string name, ref Trace trace) {
		trace = this;
		if (context) {
			if (auto result = context.search(name, trace)) {
				return result;
			}
		}
		if (upper) {
			return upper.search(name, trace);
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
	//used when check for cycles for variables and aliases
	bool process;
	SearchContext context() {
		return null;
	}
}

abstract class Statement : Node {
	bool ispure;
}

//either a type or a value
abstract class Expression : Statement {
	Expression type;
	bool lvalue;
}

class Bool : Expression {
	mixin autoChildren!();
}

class Char : Expression {
	mixin autoChildren!();
}

class Int : Expression {
	uint size;
	this(uint _) {
		size = _;
	}

	mixin autoChildren!();
}

class UInt : Expression {
	uint size;
	this(uint _) {
		size = _;
	}

	mixin autoChildren!();
}

class Metaclass : Expression {
	mixin autoChildren!();
}

abstract class Var : Statement {
	string name;
	bool heap; //has the address of the variable been taken,does not apply to closures
	bool manifest;
	Expression definition;
	Expression explicitType;
	@property Expression type() {
		return definition.type;
	}

	mixin autoChildren!definition;
}

class ModuleVar : Var {
	string[] namespace;
}

class Module : Node, SearchContext {
	ModuleVar[string] symbols;
	string[] namespace;

override:
	SearchContext context() {
		return this;
	}

	Var search(string name, ref Trace trace) {
		if (name in symbols) {
			return symbols[name];
		}
		return null;
	}

	void pass(Node) {
	}

	mixin autoChildren!(symbols);
}

class Import : Expression {
	Module mod;
	mixin autoChildren!();
}

class ImportType : Expression {
	mixin autoChildren!();
}

class IntLit : Expression {
	BigInt value;
	bool usigned;
	mixin autoChildren!();
}

class CharLit : Expression {
	dchar value;
	mixin autoChildren!();
}

class BoolLit : Expression {
	bool yes;
	mixin autoChildren!();
}

class StructLit : Expression {
	Expression[] values;
	size_t[string] names;
	mixin autoChildren!values;
}

class Variable : Expression {
	string name;
	Var definition;
	mixin autoChildren!();
}

class FuncArgument : Expression {
	FuncLit func;
	mixin autoChildren!();
}

class If : Expression {
	Expression cond;
	Expression yes;
	Expression no;
	mixin autoChildren!(cond, yes, no);
}

class While : Expression {
	Expression cond;
	Expression state;
	mixin autoChildren!(cond, state);
}

class New : Expression {
	Expression value;
	mixin autoChildren!value;
}

class NewArray : Expression {
	Expression length;
	Expression value;
	mixin autoChildren!(length, value);
}

class Cast : Expression {
	Expression value;
	Expression wanted;
	bool implicit;
	mixin autoChildren!(value, wanted);
}

class Dot : Expression {
	Expression value;
	Index index;
	Variable variable; //if value is a module, used when unaliasing
	mixin autoChildren!value;
}

//if array is a type and index is an empty struct then this is a type
class ArrayIndex : Expression {
	Expression array;
	Expression index;
	mixin autoChildren!(array, index);
}

//if fptr and arg are types then this is a type
class FCall : Expression {
	Expression fptr;
	Expression arg;
	//todo ispure for type
	mixin autoChildren!(fptr, arg);
}

class Slice : Expression {
	Expression array;
	Expression left;
	Expression right;
	mixin autoChildren!(array, left, right);
}

class Binary(string T) : Expression 
		if (["*", "/", "%", "+", "-", "~", "==", "!=",
			"<=", ">=", "<", ">", "&&", "||", "="].canFind(T)) {
	Expression left;
	Expression right;
	mixin autoChildren!(left, right);
}

class Prefix(string T) : Expression if (["+", "-", "*", "/", "&", "!"].canFind(T)) {
	Expression value;
	mixin autoChildren!value;
}

class Postfix(string T) : Expression if (["(*)"].canFind(T)) {
	Expression value;
	mixin autoChildren!value;
}

class ScopeVar : Var {
}

class Scope : Expression {
	//includes alias = for now
	//duped with iterating over context
	ScopeVar[string] symbols;
	Statement[] states;
	Expression last;

	static class ScopeContext : SearchContext {
		Scope that;
		ScopeVar[string] symbols;

		this(Scope that) {
			this.that = that;
			symbols = that.symbols.dup;
		}

		Var search(string name, ref Trace trace) {
			if (name in symbols) {
				return symbols[name];
			}
			return null;
		}

		void pass(Node node) {
			if (auto var = cast(ScopeVar) node) {
				symbols[var.name] = var;
			}
		}
	}

override:
	SearchContext context() {
		return new ScopeContext(this);
	}

	mixin autoChildren!(symbols, states);
}

class FuncLit : Expression {
	Expression explict_return; //maybe null
	Expression argument;
	Expression text;

	mixin autoChildren!(argument, text, explict_return);
}

class StringLit : Expression {
	string str;
	mixin autoChildren!();
}

class ArrayLit : Expression {
	Expression[] values;
	mixin autoChildren!values;
}

class ExternJS : Expression {
	string external;
	mixin autoChildren!type;
}
