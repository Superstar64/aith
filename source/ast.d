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
import std.meta : AliasSeq;
import std.traits : isArray, isAssociativeArray;
import std.variant : Algebraic;

import error : error, Position;

template dispatch(alias fun, Types...) {
	auto dispatch(Base, T...)(auto ref Base base, auto ref T args) {
		foreach (Type; Types) {
			if (cast(Type) base) {
				//can't copy because fun might modify base though a different reference
				return fun(*cast(Type*)&base, args);
			}
		}
		assert(0, base.to!string);
	}
}

alias Index = Algebraic!(BigInt, string);
alias SymbolTypes = AliasSeq!(FuncLit, ModuleVarDef);
alias Symbol = Algebraic!SymbolTypes;

interface SearchContext {
	VarDef search(string name, ref Trace); //trace is an out variable with is by default the current trace
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

	VarDef search(string name) {
		Trace trace;
		return search(name, trace);
	}

	VarDef search(string name, ref Trace trace) {
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
	//used when check for cycles for variables and aliases
	bool process;
	SearchContext context() {
		return null;
	}
}

abstract class Statement : Node {
	bool ispure;
}

class Assign : Statement {
	Expression left;
	Expression right;
}

abstract class VarDef : Statement {
	string name;
	bool heap; //has the address of the variable been taken,does not apply to closures
	bool manifest;
	Expression definition;
	Expression explicitType;
	@property Expression type() {
		return definition.type;
	}
}

struct Modifier {
	bool visible;
}

class ModuleVarDef : VarDef {
	Modifier modifier;

	alias modifier this;
}

class ScopeVarDef : VarDef {
	//points to function literal where it was declared
	FuncLit func;
}

class Module : Node, SearchContext {
	ModuleVarDef[string] symbols;
	Symbol[string] exports;
override:
	SearchContext context() {
		return this;
	}

	VarDef search(string name, ref Trace trace) {
		if (name in symbols) {
			return symbols[name];
		}
		return null;
	}

	void pass(Node) {
	}
}

//either a type or a value
abstract class Expression : Statement {
	Expression type;
	bool lvalue;
}

class ModuleVarRef : Expression {
	ModuleVarDef definition;
}

class ScopeVarRef : Expression {
	ScopeVarDef definition;
}

class Bool : Expression {
}

class Char : Expression {
}

class Int : Expression {
	uint size;
}

class UInt : Expression {
	uint size;
}

class Metaclass : Expression {
}

class Import : Expression {
	Module mod;
}

class IntLit : Expression {
	BigInt value;
	bool usigned;
}

class CharLit : Expression {
	dchar value;
}

class BoolLit : Expression {
	bool yes;
}

class Struct : Expression {
	Expression value;
	bool implicit;
}

class TupleLit : Expression {
	Expression[] values;
	size_t[string] names;
}

class Variable : Expression {
	string name;
}

class FuncArgument : Expression {
	FuncLit func;
}

class If : Expression {
	Expression cond;
	Expression yes;
	Expression no;
}

class While : Expression {
	Expression cond;
	Expression state;
}

class New : Expression {
	Expression value;
}

class NewArray : Expression {
	Expression length;
	Expression value;
}

class Cast : Expression {
	Expression value;
	Expression wanted;
	bool implicit;
}

class Dot : Expression {
	Expression value;
	Index index;
}

//if array is a type and index is an empty struct then this is a type
class ArrayIndex : Expression {
	Expression array;
	Expression index;
}

//if fptr and arg are types then this is a type
class FCall : Expression {
	Expression fptr;
	Expression arg;
	//todo ispure for type
}

class Slice : Expression {
	Expression array;
	Expression left;
	Expression right;
}

class Binary(string T) : Expression 
		if (["*", "/", "%", "+", "-", "~", "==", "!=",
			"<=", ">=", "<", ">", "&&", "||"].canFind(T)) {
	Expression left;
	Expression right;
}

class Prefix(string T) : Expression if (["+", "-", "*", "/", "&", "!"].canFind(T)) {
	Expression value;
}

class Postfix(string T) : Expression if (["(*)"].canFind(T)) {
	Expression value;
}

class Scope : Expression {
	//includes alias = for now
	//duped with iterating over context
	ScopeVarDef[string] symbols;
	Statement[] states;
	Expression last;

	static class ScopeContext : SearchContext {
		Scope that;
		ScopeVarDef[string] symbols;

		this(Scope that) {
			this.that = that;
			symbols = that.symbols.dup;
		}

		VarDef search(string name, ref Trace trace) {
			if (name in symbols) {
				return symbols[name];
			}
			return null;
		}

		void pass(Node node) {
			if (auto var = cast(ScopeVarDef) node) {
				symbols[var.name] = var;
			}
		}
	}

override:
	SearchContext context() {
		return new ScopeContext(this);
	}
}

class FuncLit : Expression {
	string name;
	Expression explict_return; //maybe null
	Expression argument;
	Expression text;
}

class StringLit : Expression {
	string str;
}

class ArrayLit : Expression {
	Expression[] values;
}

class ExternJS : Expression {
	string name;
}

//dark corners
class ImportType : Expression {
}

class ExternType : Expression {
}
