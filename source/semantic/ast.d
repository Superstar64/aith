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
module semantic.ast;

import std.bigint;
import std.meta;
import std.typecons;
import std.traits;

import jsast;
import genericast;

static import Codegen = codegen.ast;
static import Parser = parser.ast;

import misc.nonstrict;
import misc.position;

import semantic.astimpl : Equivalence;
public import semantic.astimpl : freeVariables, specialize, toRuntime;

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
	Expression specialize(Type[TypeVariableId] moves);
	Codegen.Expression toRuntime();
}

interface Symbol : Expression {
	bool strong();
	Codegen.Symbol toRuntime();
}

struct ModuleAlias {
	CompileTimeExpression element;
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
			if (value.type.freeVariables.length == 0) {
				result[key] = value.toRuntime();
			}
		}
		return make!(Codegen.Module)(result);
	}
}

interface Pattern : CompileTimeExpression {
	Type type();
	Pattern specialize(Type[TypeVariableId] moves);
	Codegen.Pattern toRuntime();
}

interface NamedPattern : Pattern {
	Type type();
	Variable argument();
}

interface TuplePattern : Pattern {
	Type type();
	Pattern[] matches();
}

interface FunctionLiteral : Symbol {
	Type type();
	string name();
	bool strong();
	SymbolId id();
	Pattern argument();
	Lazy!(Expression) text();
}

interface Binding : CompileTimeExpression {
	string name();
}

interface _Variable : Expression, Binding {
	Variable specialize(Type[TypeVariableId] moves);
	override Codegen.Variable toRuntime();
}

interface Variable : _Variable, Binding {
	Type type();
	string name();
	VarId id();
}

interface VariableDef : Expression {
	Type type();
	Pattern variable();
	Expression value();
	Expression last();
}

interface Import : CompileTimeExpression {
	Module mod();
}

interface IntLit : Expression {
	Type type();
	BigInt value();
}

interface CharLit : Expression {
	Type type();
	dchar value();
}

interface BoolLit : Expression {
	Type type();
	bool yes();
}

interface TupleLit : Expression {
	Type type();
	Expression[] values();
}

interface If : Expression {
	Type type();
	Expression cond();
	Expression yes();
	Expression no();
}

interface While : Expression {
	Type type();
	Expression cond();
	Expression state();
}

interface New : Expression {
	Type type();
	Expression value();
}

interface NewArray : Expression {
	Type type();
	Expression length();
	Expression value();
}

interface CastInteger : Expression {
	Type type();
	Expression value();
}

interface Length : Expression {
	Type type();
}

interface Index : Expression {
	Type type();
	Expression array();
	Expression index();
}

interface IndexAddress : Expression {
	Type type();
	Expression array();
	Expression index();
}

interface TupleIndex : Expression {
	Type type();
	Expression tuple();
	uint index();
}

interface TupleIndexAddress : Expression {
	Type type();
	Expression tuple();
	uint index();
}

interface Call : Expression {
	Type type();
	Expression calle();
	Expression argument();
}

interface Slice : Expression {
	Type type();
	Expression array();
	Expression left();
	Expression right();
}

interface Binary(string op) : Expression {
	Type type();
	Expression left();
	Expression right();
}

interface Prefix(string op) : Expression {
	Type type();
	Expression value();
}

interface Deref : Expression {
	Type type();
	Expression value();
}

interface Scope : Expression {
	Type type();
	Expression pass();
	Expression last();
}

interface Assign : Expression {
	Type type();
	Expression left();
	Expression right();
}

interface StringLit : Expression {
	Type type();
	string value();
}

interface ArrayLit : Expression {
	Type type();
	Expression[] values();
}

interface ExternJs : Expression {
	Type type();
	string name();
}

interface Type : CompileTimeExpression {
	TypeVariable[TypeVariableId] freeVariables();
	Type specialize(Type[TypeVariableId] moves);
	Codegen.Type toRuntime();
	string toString();

	Type[TypeVariableId] typeMatch(Type right, Position position);
	Type[TypeVariableId] typeMatchDispatch(TypeVariable left, Position position);
	Type[TypeVariableId] typeMatchDispatch(TypeBool left, Position position);
	Type[TypeVariableId] typeMatchDispatch(TypeChar left, Position position);
	Type[TypeVariableId] typeMatchDispatch(TypeInt left, Position position);
	Type[TypeVariableId] typeMatchDispatch(TypeStruct left, Position position);
	Type[TypeVariableId] typeMatchDispatch(TypeArray left, Position position);
	Type[TypeVariableId] typeMatchDispatch(TypeFunction left, Position position);
	Type[TypeVariableId] typeMatchDispatch(TypePointer left, Position position);

	Equivalence[] predicateInstantiateDispatch(PredicateNumber left, Position position);
	Equivalence[] predicateInstantiateDispatch(PredicateTuple left, Position position);
}

interface PredicateId {
}

interface Predicate : CompileTimeExpression {
	PredicateId id();
	TypeVariable[TypeVariableId] freeVariables();
	Predicate specialize(Type[TypeVariableId] moves);
	string toString();

	Equivalence[] predicateInstantiate(Type right, Position position);
	// this's type must match right
	Equivalence[] predicateMatch(Predicate right, Position position);
}

interface PredicateNumber : Predicate {
}

interface PredicateTuple : Predicate {
	uint index();
	Type type();
}

interface RigidContext {
	string name();
}

interface RigidVariable {
	string name();
}

interface TypeVariableId {
	string name();
}

interface TypeVariable : Type, Binding {
	TypeVariableId id();
	Predicate[PredicateId] constraints();
	RigidVariable[RigidContext] rigidity();
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
