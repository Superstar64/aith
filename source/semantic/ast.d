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
module semantic.ast;

import std.bigint;
import std.meta;
import std.typecons;
import std.traits;

import misc;
import jsast;
import genericast;

static import Codegen = codegen.ast;
static import Parser = parser.ast;
import misc;

public import semantic.astimpl : specialize, toRuntime;

//be catious about https://issues.dlang.org/show_bug.cgi?id=20312

interface CompileTimeExpression {
	Expression castToExpression();
	Symbol castToSymbol();
	Type castToType();
	Import castToImport();

	T castTo(T : Expression)() {
		return castToExpression;
	}

	T castTo(T : Symbol)() {
		return castToSymbol;
	}

	T castTo(T : Type)() {
		return castToType;
	}

	T castTo(T : Import)() {
		return castToImport;
	}
}

T castTo(T)(CompileTimeExpression expression) {
	return expression.castTo!T;
}

interface Expression : CompileTimeExpression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression specialize(Type[PolymorphicVariable] moves);
	Codegen.Expression toRuntime();
}

interface Symbol : Expression {
	bool strong();
	Codegen.Symbol toRuntime();
}

struct ModuleAlias {
	CompileTimeExpression element;
	bool visible;
}

class Module {
	ModuleAlias[string] aliases;
	Symbol[string] exports;
	Parser.ModuleVarDef[string] rawSymbols;
	Parser.ModuleVarDef[] rawSymbolsOrdered;

	Codegen.Module toRuntime() {
		import codegen.astimpl : make;

		Codegen.Symbol[string] result;
		foreach (key; exports.byKey) {
			auto value = exports[key];
			if (value.generics.length == 0) {
				result[key] = value.toRuntime();
			}
		}
		return make!(Codegen.Module)(result);
	}
}

interface Pattern : CompileTimeExpression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Pattern specialize(Type[PolymorphicVariable] moves);
	Codegen.Pattern toRuntime();
}

interface NamedPattern : Pattern {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Variable argument();
}

interface TuplePattern : Pattern {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Pattern[] matches();
}

interface FunctionLiteral : Symbol {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	string name();
	bool strong();
	SymbolId id();
	Pattern argument();
	Lazy!(Expression) text();
}

interface _Variable : Expression {
	Variable specialize(Type[PolymorphicVariable] moves);
	override Codegen.Variable toRuntime();
}

interface Variable : _Variable {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	string name();
	VarId id();
}

interface VariableDef : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Pattern variable();
	Expression value();
	Expression last();
}

interface Import : CompileTimeExpression {
	Module mod();
}

interface IntLit : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	BigInt value();
}

interface CharLit : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	dchar value();
}

interface BoolLit : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	bool yes();
}

interface TupleLit : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression[] values();
}

interface If : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression cond();
	Expression yes();
	Expression no();
}

interface While : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression cond();
	Expression state();
}

interface New : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression value();
}

interface NewArray : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression length();
	Expression value();
}

interface CastInteger : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression value();
}

interface Length : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
}

interface Index : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression array();
	Expression index();
}

interface IndexAddress : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression array();
	Expression index();
}

interface TupleIndex : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression tuple();
	uint index();
}

interface TupleIndexAddress : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression tuple();
	uint index();
}

interface Call : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression calle();
	Expression argument();
}

interface Slice : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression array();
	Expression left();
	Expression right();
}

interface Binary(string op) : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression left();
	Expression right();
}

interface Prefix(string op) : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression value();
}

interface Deref : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression value();
}

interface Scope : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression pass();
	Expression last();
}

interface Assign : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression left();
	Expression right();
	Expression last();
}

interface StringLit : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	string value();
}

interface ArrayLit : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	Expression[] values();
}

interface ExternJs : Expression {
	Type type();
	Tuple!()[PolymorphicVariable] generics();
	string name();
}

interface Type : CompileTimeExpression {
	Tuple!()[PolymorphicVariable] generics();
	Type specialize(Type[PolymorphicVariable] moves);
	Codegen.Type toRuntime();
	string toString();
}

interface PolymorphicVariable : CompileTimeExpression {
}

interface Constraint : CompileTimeExpression {
	Tuple!()[PolymorphicVariable] generics();
	Constraint specialize(Type[PolymorphicVariable] moves);
	string toString();
}

interface ConstraintNumber : Constraint {
}

interface ConstraintTuple : Constraint {
	uint index();
	Type type();
}

interface Scheme : Type {
	PolymorphicVariable variable();
	Constraint[] constraints();
}

interface TypeBool : Type {
}

interface TypeChar : Type {
}

interface TypeInt : Type {
	uint size();
	bool signed();
}

interface TypeStruct : Type {
	Type[] values();
}

interface TypeArray : Type {
	Type array();
}

interface TypeFunction : Type {
	Type result();
	Type argument();
}

interface TypePointer : Type {
	Type value();
}

alias RuntimeType(T : Pattern) = Codegen.Pattern;
alias RuntimeType(T : NamedPattern) = Codegen.NamedPattern;
alias RuntimeType(T : TuplePattern) = Codegen.TuplePattern;
alias RuntimeType(T : FunctionLiteral) = Codegen.FunctionLiteral;
alias RuntimeType(T : Variable) = Codegen.Variable;
alias RuntimeType(T : VariableDef) = Codegen.VariableDef;
alias RuntimeType(T : IntLit) = Codegen.IntLit;
alias RuntimeType(T : CharLit) = Codegen.CharLit;
alias RuntimeType(T : BoolLit) = Codegen.BoolLit;
alias RuntimeType(T : TupleLit) = Codegen.TupleLit;
alias RuntimeType(T : If) = Codegen.If;
alias RuntimeType(T : While) = Codegen.While;
alias RuntimeType(T : New) = Codegen.New;
alias RuntimeType(T : NewArray) = Codegen.NewArray;
alias RuntimeType(T : CastInteger) = Codegen.CastInteger;
alias RuntimeType(T : Length) = Codegen.Length;
alias RuntimeType(T : Index) = Codegen.Index;
alias RuntimeType(T : IndexAddress) = Codegen.IndexAddress;
alias RuntimeType(T : TupleIndex) = Codegen.TupleIndex;
alias RuntimeType(T : TupleIndexAddress) = Codegen.TupleIndexAddress;
alias RuntimeType(T : Call) = Codegen.Call;
alias RuntimeType(T : Slice) = Codegen.Slice;
alias RuntimeType(T : Binary!op, string op) = Codegen.Binary!op;
alias RuntimeType(T : Prefix!op, string op) = Codegen.Prefix!op;
alias RuntimeType(T : Deref) = Codegen.Deref;
alias RuntimeType(T : Scope) = Codegen.Scope;
alias RuntimeType(T : Assign) = Codegen.Assign;
alias RuntimeType(T : StringLit) = Codegen.StringLit;
alias RuntimeType(T : ArrayLit) = Codegen.ArrayLit;
alias RuntimeType(T : ExternJs) = Codegen.ExternJs;
alias RuntimeType(T : TypeChar) = Codegen.TypeChar;
alias RuntimeType(T : TypeBool) = Codegen.TypeBool;
alias RuntimeType(T : TypeInt) = Codegen.TypeInt;
alias RuntimeType(T : TypeStruct) = Codegen.TypeStruct;
alias RuntimeType(T : TypeArray) = Codegen.TypeArray;
alias RuntimeType(T : TypePointer) = Codegen.TypePointer;
alias RuntimeType(T : TypeFunction) = Codegen.TypeFunction;
