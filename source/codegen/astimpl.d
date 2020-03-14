/+
	Copyright (C) 2020  Freddy Angel Cubas "Superstar64"
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
module codegen.astimpl;

import std.algorithm;
import std.conv;

public import codegen.ast;
import codegen.codegen;
import jsast;

import misc.json;
import misc.getters;
import misc.container;

template make(T) {
	T make(A...)(A args) {
		return new Impl!T(args);
	}
}

class Impl(T) : T {
	mixin Getters!T;
	Json jsonify() {
		return jsonifyImpl();
	}
}

mixin template DefaultExpression() {
override:
	JsExpr generateJs(JsScope depend, Extra extra) {
		return generateJsImpl(this, depend, extra);
	}

	void generateJsVarDef(JsVariable target, JsScope depend, Extra extra) {
		generateJsVarDefImpl(this, target, depend, extra);
	}

	void generateJsVar(JsVariable target, JsScope depend, Extra extra) {
		generateJsVarImpl(this, target, depend, extra);
	}
}

mixin template DefaultSymbol() {
override:
	JsExpr generateSymbol(JsScope depend, Extra extra) {
		return generateSymbolImpl(this, depend, extra);
	}

	Symbol[SymbolId] symbols() {
		return [id: this];
	}
}

class Impl(T : Expression) : T {
	mixin Getters!T;
	mixin DefaultExpression;
	Symbol[SymbolId] symbols() {
		return symbolsImpl(this);
	}

	Json jsonify() {
		return jsonifyImpl();
	}
}

class Impl(T : FunctionLiteral) : T {
	mixin Getters!T;
	mixin DefaultExpression;
	mixin DefaultSymbol;
	Symbol[SymbolId] dependants() {
		return text.get.symbols;
	}

	Json jsonify() {
		return jsonifyImpl();
	}
}

class Impl(T : Type) : T {
	mixin Getters!T;
	string mangle() {
		return mangleImpl(this);
	}

	JsExpr compareInfo() {
		return compareInfoImpl(this);
	}

	Json jsonify() {
		return jsonifyImpl();
	}
}

Symbol[SymbolId] symbolsImpl(T : Var)(T that) {
	return null;
}

Symbol[SymbolId] symbolsImpl(T : VariableDef)(T that) {
	with (that)
		return mergeMapsLeft(value.symbols, last.symbols);
}

Symbol[SymbolId] symbolsImpl(T : IntLit)(T that) {
	return null;
}

Symbol[SymbolId] symbolsImpl(T : CharLit)(T that) {
	return null;
}

Symbol[SymbolId] symbolsImpl(T : BoolLit)(T that) {
	return null;
}

Symbol[SymbolId] symbolsImpl(T : TupleLit)(T that) {
	with (that)
		return values.map!(a => a.symbols)
			.fold!mergeMapsLeft(emptyMap!(SymbolId, Symbol));
}

Symbol[SymbolId] symbolsImpl(T : If)(T that) {
	with (that)
		return mergeMapsLeft(cond.symbols, yes.symbols, no.symbols);
}

Symbol[SymbolId] symbolsImpl(T : While)(T that) {
	with (that)
		return mergeMapsLeft(cond.symbols, state.symbols);
}

Symbol[SymbolId] symbolsImpl(T : New)(T that) {
	with (that)
		return value.symbols;
}

Symbol[SymbolId] symbolsImpl(T : NewArray)(T that) {
	with (that)
		return mergeMapsLeft(length.symbols, value.symbols);
}

Symbol[SymbolId] symbolsImpl(T : CastInteger)(T that) {
	with (that)
		return value.symbols;
}

Symbol[SymbolId] symbolsImpl(T : Length)(T that) {
	with (that)
		return null;
}

Symbol[SymbolId] symbolsImpl(T : Index)(T that) {
	with (that)
		return mergeMapsLeft(array.symbols, index.symbols);
}

Symbol[SymbolId] symbolsImpl(T : IndexAddress)(T that) {
	with (that)
		return mergeMapsLeft(array.symbols, index.symbols);
}

Symbol[SymbolId] symbolsImpl(T : TupleIndex)(T that) {
	with (that)
		return tuple.symbols;
}

Symbol[SymbolId] symbolsImpl(T : TupleIndexAddress)(T that) {
	with (that)
		return tuple.symbols;
}

Symbol[SymbolId] symbolsImpl(T : Call)(T that) {
	with (that)
		return mergeMapsLeft(calle.symbols, argument.symbols);
}

Symbol[SymbolId] symbolsImpl(T : Slice)(T that) {
	with (that)
		return mergeMapsLeft(array.symbols, left.symbols, right.symbols);
}

Symbol[SymbolId] symbolsImpl(T : Binary!op, string op)(T that) {
	with (that)
		return mergeMapsLeft(left.symbols, right.symbols);
}

Symbol[SymbolId] symbolsImpl(T : Prefix!op, string op)(T that) {
	with (that)
		return value.symbols;
}

Symbol[SymbolId] symbolsImpl(T : Deref)(T that) {
	with (that)
		return value.symbols;
}

Symbol[SymbolId] symbolsImpl(T : Scope)(T that) {
	with (that)
		return mergeMapsLeft(pass.symbols, last.symbols);
}

Symbol[SymbolId] symbolsImpl(T : Assign)(T that) {
	with (that)
		return mergeMapsLeft(left.symbols, right.symbols);
}

Symbol[SymbolId] symbolsImpl(T : StringLit)(T that) {
	with (that)
		return null;
}

Symbol[SymbolId] symbolsImpl(T : ArrayLit)(T that) {
	with (that)
		return values.map!(a => a.symbols)
			.fold!mergeMapsLeft(emptyMap!(SymbolId, Symbol));
}

Symbol[SymbolId] symbolsImpl(T : ExternJs)(T that) {
	with (that)
		return null;
}

string mangleImpl(TypeBool) {
	return "boolean";
}

string mangleImpl(TypeChar) {
	return "character";
}

string mangleImpl(TypeInt that) {
	with (that)
		return (signed ? "integer" : "natural") ~ size.to!string;
}

string mangleImpl(TypeStruct that) {
	with (that) {
		if (values.length == 0) {
			return "void";
		}
		return "tuple_of_" ~ values[0 .. $ - 1].map!(a => a.mangle ~ "_and_")
			.joiner
			.to!string ~ values[$ - 1].mangle ~ "_end";
	}
}

string mangleImpl(TypeArray that) {
	with (that)
		return array.mangle ~ "_array";
}

string mangleImpl(TypeFunction that) {
	with (that)
		return "function_of_" ~ argument.mangle ~ "_to_" ~ result.mangle ~ "_end";
}

string mangleImpl(TypePointer that) {
	with (that)
		return value.mangle ~ "_pointer";
}
