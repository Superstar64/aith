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

import std.algorithm : canFind;
import std.bigint;
import std.meta;
import std.typecons;
import std.traits;

import misc.container;

import jsast;

import misc.nonstrict;
import misc.position;

import semantic.astimpl : Equivalence;
import semantic.semantic : RecursionChecker;
public import semantic.astimpl : freeVariables, specialize;

//be catious about https://issues.dlang.org/show_bug.cgi?id=20312

struct ModuleDefinition {
	Expression get;
	bool freshen;
}

class Module {
	Dictonary!(string, ModuleDefinition delegate(RecursionChecker)) aliases;
	ModuleDefinition delegate(RecursionChecker)[] orderedAliases;
}

ModuleDefinition get(ModuleDefinition delegate(RecursionChecker) that) {
	return that(RecursionChecker());
}

interface Expression {
}

interface Term : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	Type type();
	Term specialize(Dictonary!(TypeVariableId, Type) moves);
	Dictonary!(Tuple!(SymbolId, TypeHash), Symbol) symbols();
	Js.JsExpr generateJs(Js.JsScope depend, Extra extra);
}

class SymbolId {
}

enum Linkage {
	strong,
	weak,
	inner
};

interface Symbol : Term {
	import codegen.codegen : Extra;
	import Js = jsast;

	string name();
	Linkage linkage();
	SymbolId id();
	Dictonary!(Tuple!(SymbolId, TypeHash), Symbol) dependants();
	Js.JsExpr generateSymbol(Js.JsScope depend, Extra extra);
}

interface Pattern : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	import semantic.semantic : Context;

	Type type();
	Pattern specialize(Dictonary!(TypeVariableId, Type) moves);
	Js.JsPattern generatePatternMatch(Extra extra);
	void removeBindings(Context context, Position position);
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
	Linkage linkage();
	SymbolId id();
	Pattern argument();
	Lazy!(Term) text();
}

interface Binding : Expression {
	string name();
}

interface _Variable : Term, Binding {
	Variable specialize(Dictonary!(TypeVariableId, Type) moves);
}

class VarId {
}

interface Variable : _Variable, Binding {
	Type type();
	string name();
	VarId id();
}

interface VariableDefinition : Term {
	Type type();
	Pattern variable();
	Term value();
	Term last();
}

interface Call : Term {
	Type type();
	Term calle();
	Term argument();
}

interface Desugar(string name) : Term if (["new", "new array", "length", "index", "index address", "slice", "and", "or", "not", "derefence", "assign", "delete", "borrow", "delete array", "borrow array"].canFind(name)) {
	Type type();
}

interface DesugarContext(string name) : Term if (["equal", "not equal", "less equal", "greater equal", "less", "greater", "multiply", "divide", "modulus", "add", "subtract", "negate"].canFind(name)) {
	Type type();
	Type context();
}

interface Import : Expression {
	Module mod();
}

interface IntLit : Term {
	Type type();
	BigInt value();
}

interface CharLit : Term {
	Type type();
	dchar value();
}

interface BoolLit : Term {
	Type type();
	bool yes();
}

interface TupleLit : Term {
	Type type();
	Term[] values();
}

interface If : Term {
	Type type();
	Term cond();
	Term yes();
	Term no();
}

interface CastInteger : Term {
	Type type();
	Type contextWanted();
	Type contextInput();
}

interface TupleIndex : Term {
	Type type();
	uint index();
}

interface TupleIndexAddress : Term {
	Type type();
	uint index();
	Type context();
}

interface StringLit : Term {
	Type type();
	string value();
}

interface ArrayLit : Term {
	Type type();
	Term[] values();
}

interface ExternJs : Term {
	Type type();
	string name();
}

struct TypeHash {
	string hash;
}

interface Type : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	Dictonary!(TypeVariableId, TypeVariable) freeVariables();
	Type specialize(Dictonary!(TypeVariableId, Type) moves);
	string toString();

	Dictonary!(TypeVariableId, Type) typeMatch(Type right, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeVariable left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeBool left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeChar left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeInt left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeStruct left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeArray left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeFunction left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypePointer left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeOwnPointer left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeOwnArray left, Position position);
	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeWorld left, Position position);

	Dictonary!(TypeVariableId, Type) predicateInstantiateDispatch(PredicateEqual left, Dictonary!(TypeVariableId, Type) current, Position position);
	Dictonary!(TypeVariableId, Type) predicateInstantiateDispatch(PredicateNumber left, Dictonary!(TypeVariableId, Type) current, Position position);
	Dictonary!(TypeVariableId, Type) predicateInstantiateDispatch(PredicateTuple left, Dictonary!(TypeVariableId, Type) current, Position position);
	Dictonary!(TypeVariableId, Type) predicateInstantiateDispatch(PredicateUnrestricted left, Dictonary!(TypeVariableId, Type) current, Position position);

	string mangle();
	Js.JsExpr compareInfo(Extra extra);

}

TypeHash typeHash(Type type) {
	return TypeHash(type.mangle);
}

interface PredicateId {
}

interface Predicate : Expression {
	PredicateId id();
	Dictonary!(TypeVariableId, TypeVariable) freeVariables();
	Predicate specialize(Dictonary!(TypeVariableId, Type) moves);
	string toString();

	Dictonary!(TypeVariableId, Type) predicateInstantiate(Type right, Dictonary!(TypeVariableId, Type) current, Position position);
	// this's type must match right
	Dictonary!(TypeVariableId, Type) predicateMatch(Predicate right, Dictonary!(TypeVariableId, Type) current, Position position);
}

interface PredicateEqual : Predicate {
}

interface PredicateNumber : Predicate {
}

interface PredicateTuple : Predicate {
	uint index();
	Type type();
}

interface PredicateUnrestricted : Predicate {
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
	Dictonary!(PredicateId, Predicate) constraints();
	Dictonary!(RigidContext, RigidVariable) rigidity();
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

interface TypeOwnPointer : Type {
	Type value();
}

interface TypeOwnArray : Type {
	Type array();
}

interface TypeWorld : Type {
}
