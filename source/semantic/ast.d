/+
	Copyright (C) 2020  Freddy Angel Cubas "Superstar64"
	This file is part of Aith.

	Aith is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation version 3 of the License.

	Aith is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with Aith.  If not, see <http://www.gnu.org/licenses/>.
+/
module semantic.ast;

import std.algorithm : canFind;
import std.bigint;
import std.meta;
import std.typecons;
import std.traits;

import misc.nonstrict;
import misc.position;
import misc.container;

import jsast;

import semantic.semantic : RecursionChecker;
public import semantic.astimpl : freeVariables, substitute;

//be catious about https://issues.dlang.org/show_bug.cgi?id=20312

struct ModuleDefinition {
	Expression matrix;
	// these are ignored if matrix is not a term
	Dictonary!(TypeVariableId, TypeRequirement) typePrefix;
	Dictonary!(StageVariableId, StageRequirement) stagePrefix;
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

interface Import : Expression {
	Module mod();
}

interface Term : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	Type type();
	Term substitute(Dictonary!(TypeVariableId, Type) moves);
	Term substitute(Dictonary!(RigidVariableId, Type) moves);
	Term substitute(Dictonary!(StageVariableId, Stage) moves);
	Term substitute(Dictonary!(VariableId, Term) moves);
	Term substitute(Dictonary!(VariableId, VariableId) moves);
	// only for removing symbol forward references
	Term substitute(Lazy!(Dictonary!(SymbolId, Term)) moves);
	Term alphaConvert();
	Term reduceMacros();

	Js.JsExpr generateJs(Js.JsScope depend, Extra extra);
}

struct SymbolId {
	size_t raw;
}

interface SymbolForwardReference : Term {
	Type type();
	SymbolId id();
}

enum Linkage {
	strong,
	weak,
}

interface SymbolReference : Term {
	Type type();
	string name();
	Linkage linkage();
	SymbolId id();
	Lazy!Term source();
	Tuple!(Type, Predicate)[] dictonaries();
}

interface ExternJs : Term {
	Type type();
	string name();
	Tuple!(Type, Predicate)[] dictonaries();
}

struct Argument {
	VariableId id;
	string name;
}

interface MacroFunctionLiteral : Term {
	Type type();
	Argument argument();
	Term text();
}

class VariableId {
}

interface Variable : Term {
	Type type();
	string name();
	VariableId id();
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

interface MacroCall : Term {
	Type type();
	Term calle();
	Term argument();
}

interface If : Term {
	Type type();
	Term cond();
	Term yes();
	Term no();
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

interface StringLit : Term {
	Type type();
	string value();
}

interface ArrayLit : Term {
	Type type();
	Term[] values();
}

interface Pattern : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	import semantic.semantic : Context;

	Type type();
	Pattern substitute(Dictonary!(TypeVariableId, Type) moves);
	Pattern substitute(Dictonary!(RigidVariableId, Type) moves);
	Pattern substitute(Dictonary!(StageVariableId, Stage) moves);
	Pattern substitute(Dictonary!(VariableId, VariableId) moves);
	Js.JsPattern generatePatternMatch(Extra extra);
	Tuple!(Variable, bool)[] orderedBindings();
}

interface NamedPattern : Pattern {
	Type type();
	VariableId id();
	string name();
	bool shadow();
}

interface TuplePattern : Pattern {
	Type type();
	Pattern[] matches();
}

enum TypePrecedence {
	zero,
	arrow,
	raw,
	top
}

interface Type : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	Stage type();
	Set!TypeVariableId freeVariables();
	TypeVariableId[] freeVariablesOrdered();
	Type substitute(Dictonary!(TypeVariableId, Type) moves);
	Type substitute(Dictonary!(RigidVariableId, Type) moves);
	Type substitute(Dictonary!(StageVariableId, Stage) moves);
	string toStringPrecedence(TypePrecedence);
	final toString() {
		return toStringPrecedence(TypePrecedence.zero);
	}

	void unify(Type right, Position, TypeSystem);
	void unifyDispatch(TypeVariable left, Position, TypeSystem);
	void unifyDispatch(TypeVariableRigid left, Position, TypeSystem);
	void unifyDispatch(TypeBool left, Position, TypeSystem);
	void unifyDispatch(TypeChar left, Position, TypeSystem);
	void unifyDispatch(TypeInt left, Position, TypeSystem);
	void unifyDispatch(TypeStruct left, Position, TypeSystem);
	void unifyDispatch(TypeArray left, Position, TypeSystem);
	void unifyDispatch(TypeFunction left, Position, TypeSystem);
	void unifyDispatch(TypeMacro left, Position, TypeSystem);
	void unifyDispatch(TypePointer left, Position, TypeSystem);
	void unifyDispatch(TypeOwnPointer left, Position, TypeSystem);
	void unifyDispatch(TypeOwnArray left, Position, TypeSystem);
	void unifyDispatch(TypeWorld left, Position, TypeSystem);

	void checkDispatch(PredicateEqual left, Position, TypeSystem);
	void checkDispatch(PredicateNumber left, Position, TypeSystem);
	void checkDispatch(PredicateTuple left, Position, TypeSystem);
	void checkDispatch(PredicateUnrestricted left, Position, TypeSystem);

	Js.JsExpr info(PredicateEqual, Extra extra);
	Js.JsExpr info(PredicateNumber, Extra extra);
	Js.JsExpr info(PredicateTuple, Extra extra);
	Js.JsExpr info(PredicateUnrestricted, Extra extra);
}

struct RigidContextId {
	size_t raw;
}

struct RigidVariableId {
	size_t raw;
}

interface TypeVariableRigid : Type {
	Stage type();
	RigidVariableId id();
	string name();
	RigidContextId context();
}

struct TypeVariableId {
	size_t raw;
}

interface TypeVariable : Type {
	Stage type();
	TypeVariableId id();
}

interface TypeBool : Type {
	Stage type();
}

interface TypeChar : Type {
	Stage type();
}

interface TypeInt : Type {
	Stage type();
	uint size();
	bool signed();
}

interface TypeStruct : Type {
	Stage type();
	Type[] values();
}

interface TypeFunction : Type {
	Stage type();
	Type result();
	Type argument();
}

interface TypeMacro : Type {
	Stage type();
	Type result();
	Type argument();
}

interface TypeArray : Type {
	Stage type();
	Type value();
}

interface TypeOwnArray : Type {
	Stage type();
	Type value();
}

interface TypePointer : Type {
	Stage type();
	Type value();
}

interface TypeOwnPointer : Type {
	Stage type();
	Type value();
}

interface TypeWorld : Type {
	Stage type();
}

class PredicateId {
}

interface Predicate : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	PredicateId id();
	Set!TypeVariableId freeVariables();
	TypeVariableId[] freeVariablesOrdered();

	Predicate substitute(Dictonary!(TypeVariableId, Type) moves);
	Predicate substitute(Dictonary!(RigidVariableId, Type) moves);
	Predicate substitute(Dictonary!(StageVariableId, Stage) moves);
	string toString();

	void check(Type right, Position, TypeSystem);
	TypeAlgebra[] decompose(Predicate right, Position);

	bool compare(Predicate right);
	bool compareDispatch(PredicateUnrestricted left);
	bool compareDispatch(PredicateEqual left);
	bool compareDispatch(PredicateNumber left);
	bool compareDispatch(PredicateTuple left);

	Js.JsExpr typeInfo(Type type, Extra extra);
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

enum StagePrecedence {
	zero,
	arrow,
	top
}

interface Stage : Expression {
	Set!StageVariableId freeVariables();
	Stage substitute(Dictonary!(StageVariableId, Stage) moves);

	string toStringPrecedence(StagePrecedence);
	final toString() {
		return toStringPrecedence(StagePrecedence.zero);
	}

	void unify(Stage right, Position, StageSystem);
	void unifyMatch(StageRuntime left, Position, StageSystem);
	void unifyMatch(StageMacro left, Position, StageSystem);
	void unifyMatch(StageVariable left, Position, StageSystem);
}

struct StageVariableId {
	size_t raw;
}

interface StageVariable : Stage {
	StageVariableId id();
}

interface StageRuntime : Stage {
}

interface StageMacro : Stage {
	Stage result();
	Stage argument();
}

interface StagePredicateId {
}

interface StagePredicate : Expression {
	StagePredicateId id();
	StagePredicate substitute(Dictonary!(StageVariableId, Stage) moves);
	Set!StageVariableId freeVariables();
	StageAlgebra[] decompose(StagePredicate right, Position);

	void check(Stage right, Position, StageSystem);
}

interface TypeAlgebra {
	TypeAlgebra substitute(Dictonary!(TypeVariableId, Type) moves);
	TypeAlgebra substitute(Dictonary!(RigidVariableId, Type) moves);
	Set!TypeVariableId freeVariables();
	void reduce(TypeSystem);

	string toString();
}

interface TypeEquation : TypeAlgebra {
	Type left();
	Type right();
	Position position();
}

interface TypePredicateCall : TypeAlgebra {
	Predicate predicate();
	Type type();
	Position position();
}

struct TypeRequirement {
	Position position;
	Stage type;
	Dictonary!(PredicateId, Predicate) predicates;
	TypeRequirement substitute(Dictonary!(StageVariableId, Stage) substitution) {
		return TypeRequirement(position, type.substitute(substitution), predicates.substitute(substitution));
	}
}

struct RigidRequirement {
	Position position;
	Stage type;
	Dictonary!(PredicateId, Predicate) predicates;
	RigidRequirement substitute(Dictonary!(StageVariableId, Stage) substitution) {
		return RigidRequirement(position, type.substitute(substitution), predicates.substitute(substitution));
	}
}

class TypeSystem {
	TypeAlgebra[] algebra;
	Dictonary!(TypeVariableId, Type) substitution;
	Dictonary!(TypeVariableId, TypeRequirement) unsolved;
	Dictonary!(RigidVariableId, Type) substitutionRigid;
	Dictonary!(RigidVariableId, RigidRequirement) unsolvedRigid;
	StageSystem parent;

	this(TypeAlgebra[] algebra, Dictonary!(TypeVariableId, TypeRequirement) unsolved, Dictonary!(RigidVariableId, RigidRequirement) unsolvedRigid, StageSystem parent) {
		assert(isSubSet(algebra.freeVariables, unsolved.keys));
		this.algebra = algebra;
		this.unsolved = unsolved;
		this.unsolvedRigid = unsolvedRigid;
		this.parent = parent;
	}
}

interface StageAlgebra {
	StageAlgebra substitute(Dictonary!(StageVariableId, Stage) moves);
	Set!StageVariableId freeVariables();
	void reduce(StageSystem);

	string toString();
}

interface StageEquation : StageAlgebra {
	Stage left();
	Stage right();
	Position position();
}

interface StagePredicateCall : StageAlgebra {
	StagePredicate predicate();
	Stage type();
	Position position();
}

struct StageRequirement {
	Position position;
	Dictonary!(StagePredicateId, StagePredicate) predicates;
}

class StageSystem {
	StageAlgebra[] algebra;
	Dictonary!(StageVariableId, Stage) substitution;
	Dictonary!(StageVariableId, StageRequirement) unsolved;
	this(StageAlgebra[] algebra, Dictonary!(StageVariableId, StageRequirement) unsolved) {
		assert(isSubSet(algebra.freeVariables, unsolved.keys));
		this.algebra = algebra;
		this.unsolved = unsolved;
	}
}
