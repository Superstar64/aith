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
module semanticast;

import std.algorithm : all, canFind, filter, map;
import std.array : array;
import std.bigint : BigInt;
import std.range : chain, only, retro, zip;
import std.meta : AliasSeq;
import std.typecons : Tuple;

static import Parser = parserast;
import error : error, Position;
import misc;

struct Wrapper(T) {
	T _value;
	Position position;
	alias _value this;
}

abstract class Node {
}

interface Symbol {
	string getName();
	final string name() {
		return getName();
	}
}

class Module : Node, SearchContext {
	Wrapper!Expression[string] aliases;
	Tuple!()[string] visible;
	Symbol[string] exports;

	Parser.ModuleVarDef[string] rawSymbols;
override:
	Expression search(string name) {
		if (name in aliases) {
			return aliases[name];
		}
		if (name in rawSymbols) {
			import semantic : processModuleSymbol;

			processModuleSymbol(this, rawSymbols[name]);
			return aliases[name];
		}
		return null;
	}
}

class ModuleVarDef : Node, Symbol {
	Wrapper!Expression value;
	bool visible;
	string name;
	this(Wrapper!Expression value, bool visible, string name) {
		this.value = value;
		this.visible = visible;
		this.name = name;
	}

	override final string getName() {
		return this.name;
	}
}

interface SearchContext {
	Expression search(string name);
}

struct Context {
	Module global;
	FuncLit local;
	//used for checking variables don't escape
	Tuple!()[ScopeVarDef] localVariables;
	//includes module
	SearchContext[] searchSpace;
	Expression search(string name) {
		auto range = searchSpace.retro.map!(a => a.search(name)).filter!(a => a !is null);
		return range.empty ? null : range.front;
	}
}

abstract class Statement : Node {
	bool ispure;
	this() {
	}

	this(bool ispure) {
		this.ispure = ispure;
	}
}

//either a type or a value
abstract class Expression : Statement {
	Type type;
	bool lvalue;
	this() {
	}

	this(Type type, bool lvalue, bool ispure) {
		super(ispure);
		this.type = type;
		this.lvalue = lvalue;
	}
}

abstract class Literal : Expression {
	this(Type type) {
		super(type, false, true);
	}
}

class StructFunc : Literal {
	this() {
		super(new TypeStructFunc());
	}
};

class CastFunc : Literal {
	this() {
		super(new TypeCastFunc());
	}
};

class CastPartial : Literal {
	Type value;
	this(Type value) {
		super(new TypeCastPartial());
		this.value = value;
	}
};

abstract class Type : Literal {
	this() {
		super(metaclass);
	}
}

class ModuleVarRef : Expression {
	Wrapper!ModuleVarDef definition;
	this(Wrapper!ModuleVarDef definition) {
		super(definition.value.type, true, false);
		this.definition = definition;
	}
}

class TypeBool : Type {
}

class TypeChar : Type {
}

class TypeInt : Type {
	uint size;
	this(int size) {
		super();
		this.size = size;
	}
}

class TypeUInt : Type {
	uint size;
	this(int size) {
		super();
		this.size = size;
	}
}

class TypeMetaclass : Type {
	this() {
	}
}

TypeMetaclass metaclass;
static this() {
	metaclass = new TypeMetaclass();
	metaclass.type = metaclass;
	metaclass.ispure = true;
}

class Import : Literal {
	Module mod;
	this(Module mod) {
		super(new TypeImport());
		this.mod = mod;
	}
}

class IntLit : Literal {
	BigInt value;
	this(BigInt value) {
		super(new TypeInt(0));
		this.value = value;
	}
}

class CharLit : Literal {
	dchar value;
	this(dchar value) {
		super(new TypeChar);
		this.value = value;
	}
}

class BoolLit : Literal {
	bool yes;
	this(bool value) {
		super(new TypeBool);
		this.yes = value;
	}
}

class TypeStruct : Type {
	Type[] values;
	this() {
		this([]);
	}

	this(Type[] values) {
		super();
		this.values = values;
	}
}

class TupleLit : Expression {
	Wrapper!Expression[] values;
	this(Wrapper!Expression[] values) {
		super(new TypeStruct(values.map!(a => a.type).array), false,
				values.map!(a => a.ispure).all);
		this.values = values;
	}
}

class Variable : Expression {
	string name;
}

class FuncArgument : Expression {
	this(Type type) {
		//todo make lvalue
		super(type, false, true);
	}
}

class If : Expression {
	Wrapper!Expression cond;
	Wrapper!Expression yes;
	Wrapper!Expression no;
	this(Wrapper!Expression cond, Wrapper!Expression yes, Wrapper!Expression no) {
		super(yes.type, false, cond.ispure && yes.ispure && no.ispure);
		this.cond = cond;
		this.yes = yes;
		this.no = no;
	}
}

class While : Expression {
	Wrapper!Expression cond;
	Wrapper!Expression state;
	this(Wrapper!Expression cond, Wrapper!Expression state) {
		super(new TypeStruct(), false, cond.ispure && state.ispure);
		this.cond = cond;
		this.state = state;
	}
}

class New : Expression {
	Wrapper!Expression value;
	this(Wrapper!Expression value) {
		super(new TypePointer(value.type), false, value.ispure);
		this.value = value;
	}
}

class NewArray : Expression {
	Wrapper!Expression length;
	Wrapper!Expression value;
	this(Wrapper!Expression length, Wrapper!Expression value) {
		super(new TypeArray(value.type), false, length.ispure && value.ispure);
		this.length = length;
		this.value = value;
	}
}

class CastInteger : Expression {
	Wrapper!Expression value;
	Wrapper!Type wanted;
	this(Wrapper!Expression value, Wrapper!Type wanted) {
		super(wanted, false, value.ispure);
		this.value = value;
		this.wanted = wanted;
	}
}

class CastExtern : Expression {
	Wrapper!ExternJs value;
	Wrapper!Type wanted;
	this(Wrapper!ExternJs value, Wrapper!Type wanted) {
		super(wanted, false, value.ispure);
		this.value = value;
		this.wanted = wanted;
	}
}

class Length : Expression {
	Wrapper!Expression value;
	this(Wrapper!Expression value) {
		super(new TypeUInt(0), value.lvalue, value.ispure);
		this.value = value;
	}
}

class Index : Expression {
	Wrapper!Expression array;
	Wrapper!Expression index;
	this(Wrapper!Expression array, Wrapper!Expression index) {
		super(array.type.castTo!TypeArray.array, true, array.ispure && index.ispure);
		this.array = array;
		this.index = index;
	}
}

class TupleIndex : Expression {
	Wrapper!Expression tuple;
	uint index;
	this(Wrapper!Expression tuple, uint index) {
		super(tuple.type.castTo!TypeStruct.values[index], tuple.lvalue, tuple.ispure);
		this.tuple = tuple;
		this.index = index;
	}
}

class TypeArray : Type {
	Type array;

	this(Type array) {
		super();
		this.array = array;
	}
}

class Call : Expression {
	Wrapper!Expression calle;
	Wrapper!Expression argument;
	//todo ispure for type
	this(Wrapper!Expression calle, Wrapper!Expression argument) {
		super(calle.type.castTo!TypeFunction.calle, false, false);
		this.calle = calle;
		this.argument = argument;
	}
}

class TypeFunction : Type {
	Type calle;
	Type argument;

	this(Type calle, Type argument) {
		super();
		this.calle = calle;
		this.argument = argument;
	}
}

class Slice : Expression {
	Wrapper!Expression array;
	Wrapper!Expression left;
	Wrapper!Expression right;
	this(Wrapper!Expression array, Wrapper!Expression left, Wrapper!Expression right) {
		super(array.type, false, array.ispure && left.ispure && right.ispure);
		this.array = array;
		this.left = left;
		this.right = right;
	}
}

class Binary(string op) : Expression 
		if (["*", "/", "%", "+", "-", "~", "==",
			"!=", "<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
	Wrapper!Expression left;
	Wrapper!Expression right;
	this(Wrapper!Expression left, Wrapper!Expression right) {
		static if (["*", "/", "%", "+", "-"].canFind(op)) {
			auto type = left.type;
		} else {
			auto type = new TypeBool();
		}
		super(type, false, left.ispure && right.ispure);
		this.left = left;
		this.right = right;
	}
}

class Prefix(string op) : Expression if (["+", "-", "*", "/", "&", "!"].canFind(op)) {
	Wrapper!Expression value;
	this(Wrapper!Expression value) {
		bool lvalue;
		static if (op == "-") {
			auto type = value.type;
		} else static if (op == "*") {
			auto type = value.type.castTo!TypePointer.value;
			lvalue = true;
		} else static if (op == "&") {
			auto type = new TypePointer(value.type);
		} else static if (op == "!") {
			auto type = new TypeBool;
		} else {
			assert(0, op ~ "not supported");
		}
		super(type, lvalue, value.ispure);
		this.value = value;
	}
}

class TypePointer : Type {
	Type value;

	this(Type value) {
		super();
		this.value = value;
	}
}

class Scope : Expression {
	Wrapper!Statement[] states;
	Wrapper!Expression last;
	this(Wrapper!Statement[] states, Wrapper!Expression last) {
		super(last.type, false, states.chain(last.only).map!(a => a.ispure).all);
		this.states = states;
		this.last = last;
	}
}

class ScopeVarDef : Statement {
	string name;
	Wrapper!Expression value;
	this(string name, Wrapper!Expression value) {
		super(value.ispure);
		this.name = name;
		this.value = value;
	}
}

class ScopeVarRef : Expression {
	Wrapper!ScopeVarDef definition;
	this(Wrapper!ScopeVarDef definition) {
		super(definition.value.type, true, true);
		this.definition = definition;
	}
}

class Assign : Statement {
	Wrapper!Expression left;
	Wrapper!Expression right;
	this(Wrapper!Expression left, Wrapper!Expression right) {
		super(left.ispure && right.ispure);
		this.left = left;
		this.right = right;
	}
}

class ScopeSearcher : SearchContext {
	ScopeVarRef[string] variables;
override:
	Expression search(string name) {
		if (name in variables) {
			return variables[name];
		}
		return null;
	}
}

class FuncLit : Literal, Symbol {
	string name;
	Wrapper!Type explicitReturn; //maybe null
	Wrapper!Type argument;
	Wrapper!Expression text;
	this(string name, Wrapper!Type explicitReturn, Wrapper!Type argument) {
		if (explicitReturn) {
			super(new TypeFunction(explicitReturn, argument));
		} else {
			super(new TypeLess);
		}
		this.name = name;
		this.explicitReturn = explicitReturn;
		this.argument = argument;
	}

	override string getName() {
		return name;
	}
}

class StringLit : Literal {
	string value;
	this(string value) {
		super(new TypeArray(new TypeChar()));
		this.value = value;
	}
}

class ArrayLit : Expression {
	Wrapper!Expression[] values;
	this(Wrapper!Expression[] values) {
		super(new TypeArray(values[0].type), false, values.map!(a => a.ispure).all);
		this.values = values;
	}
}

class ExternJs : Expression {
	string name;
	this(string name) {
		super(new TypeExtern, true, true);
		this.name = name;
	}
}

class TypeLess : Type {
}

//dark corners
class TypeImport : TypeLess {
}

class TypeExtern : TypeLess {
}

class TypeStructFunc : TypeLess {
};

class TypeCastFunc : TypeLess {
};

class TypeCastPartial : TypeLess {
};

bool sameType(Type a, Type b) {
	alias Types = AliasSeq!(TypeMetaclass, TypeBool, TypeChar, TypeInt, TypeUInt,
			TypeStruct, TypePointer, TypeArray, TypeFunction, TypeImport, TypeExtern);
	return dispatch!((a, b) => dispatch!((a, b) => sameTypeImpl(b, a), Types)(b, a), Types)(a, b);
}

bool sameTypeImpl(T1, T2)(T1 a, T2 b) {
	static if (!is(T1 == T2) || is(T1 == TypeImport) || is(T1 == TypeExtern)) {
		return false;
	} else {
		return sameTypeImpl2(a, b);
	}
}

bool sameTypeImpl2(T)(T a, T b)
		if (is(T == TypeBool) || is(T == TypeChar) || is(T == TypeMetaclass)) {
	return true;
}

bool sameTypeImpl2(T)(T a, T b) if (is(T == TypeUInt) || is(T == TypeInt)) {
	return a.size == b.size;
}

bool sameTypeImpl2(TypeStruct a, TypeStruct b) {
	return a.values.length == b.values.length && zip(a.values, b.values)
		.map!(a => sameType(a[0], a[1])).all;
}

bool sameTypeImpl2(TypePointer a, TypePointer b) {
	return sameType(a.value, b.value);
}

bool sameTypeImpl2(TypeArray a, TypeArray b) {
	return sameType(a.array, b.array);
}

bool sameTypeImpl2(TypeFunction a, TypeFunction b) {
	return sameType(a.calle, b.calle) && sameType(a.argument, b.argument);
}
