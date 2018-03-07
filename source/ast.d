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

import std.algorithm : any, canFind, filter, joiner, map;
import std.bigint : BigInt;
import std.conv : to;
import std.range : chain, generate, tee;
import std.meta : AliasSeq;
import std.traits : isArray, isAssociativeArray;
import std.typecons : tuple;
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

//D doesn't support multiple inheritance :<
alias SymbolTypes = AliasSeq!(FuncLit, ModuleVarDef);
alias Symbol = Algebraic!SymbolTypes;

interface SearchContext {
	VarDef search(string name);
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
}

auto range(Trace* trace) {
	static struct Range {
		Trace* front;
		bool empty() {
			return !front;
		}

		void popFront() {
			front = front.upper;
		}
	}

	return Range(trace);
}

bool cycle(Node node, Trace* trace) {
	return trace.range.any!(a => a.node == node);
}

VarDef search(Trace* trace, string name) {
	Trace* variableScope;
	return search(trace, name, variableScope);
}

VarDef search(Trace* trace, string name, ref Trace* variableScope) {
	auto range = trace.range.filter!(a => !!a.context).map!(a => tuple(a,
			a.context.search(name))).filter!(a => !!a[1]);
	if (!range.empty) {
		variableScope = range.front[0];
		return range.front[1];
	}
	return null;
}

struct Replaceable(T) {
	T _value;
	//ordered from old .. new
	T[] _original;
	alias _value this;
}

abstract class Node { //base class for all ast nodes
	Position position;
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
	Replaceable!Expression left;
	Replaceable!Expression right;
}

abstract class VarDef : Statement {
	string name;
	bool manifest;
	Replaceable!Expression definition;
	Replaceable!Expression explicitType;
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

	VarDef search(string name) {
		if (name in symbols) {
			return symbols[name];
		}
		return null;
	}
}

//either a type or a value
abstract class Expression : Statement {
	Replaceable!Expression type;
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
	Replaceable!Expression value;
	bool implicit;
}

class TupleLit : Expression {
	Replaceable!Expression[] values;
}

class Variable : Expression {
	string name;
}

class FuncArgument : Expression {
}

class If : Expression {
	Replaceable!Expression cond;
	Replaceable!Expression yes;
	Replaceable!Expression no;
}

class While : Expression {
	Replaceable!Expression cond;
	Replaceable!Expression state;
}

class New : Expression {
	Replaceable!Expression value;
}

class NewArray : Expression {
	Replaceable!Expression length;
	Replaceable!Expression value;
}

class Cast : Expression {
	Replaceable!Expression value;
	Replaceable!Expression wanted;
	bool implicit;
}

class Dot : Expression {
	Replaceable!Expression value;
	string index;
}

//if array is a type and index is an empty struct then this is a type
class Index : Expression {
	Replaceable!Expression array;
	Replaceable!Expression index;
}

//if fptr and arg are types then this is a type
class Call : Expression {
	Replaceable!Expression fptr;
	Replaceable!Expression arg;
	//todo ispure for type
}

class Slice : Expression {
	Replaceable!Expression array;
	Replaceable!Expression left;
	Replaceable!Expression right;
}

class Binary(string T) : Expression 
		if (["*", "/", "%", "+", "-", "~", "==", "!=",
			"<=", ">=", "<", ">", "&&", "||"].canFind(T)) {
	Replaceable!Expression left;
	Replaceable!Expression right;
}

class Prefix(string T) : Expression if (["+", "-", "*", "/", "&", "!"].canFind(T)) {
	Replaceable!Expression value;
}

class Postfix(string T) : Expression if (["(*)"].canFind(T)) {
	Replaceable!Expression value;
}

class Scope : Expression {
	Replaceable!Statement[] states;
	Replaceable!Expression last;

	static class ScopeContext : SearchContext {
		ScopeVarDef[string] symbols;

		VarDef search(string name) {
			if (name in symbols) {
				return symbols[name];
			}
			return null;
		}
	}

	//use this when iterating with a trace
	//variable definitions might change the search context
	final auto children(Trace* trace) {
		auto context = cast(ScopeContext) trace.context;
		void pass(Statement state) {
			if (auto var = cast(ScopeVarDef) state) {
				context.symbols[var.name] = var;
			}
		}

		return states.tee!(pass);
	}

override:
	SearchContext context() {
		return new ScopeContext();
	}
}

class FuncLit : Expression {
	string name;
	Replaceable!Expression explict_return; //maybe null
	Replaceable!Expression argument;
	Replaceable!Expression text;
}

class StringLit : Expression {
	string str;
}

class ArrayLit : Expression {
	Replaceable!Expression[] values;
}

class ExternJs : Expression {
	string name;
}

//dark corners
class ImportType : Expression {
}

class ExternType : Expression {
}
