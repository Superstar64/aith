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
import std.variant;

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
	SymbolId delegate()[] exports;
}

ModuleDefinition get(ModuleDefinition delegate(RecursionChecker) that) {
	return that(RecursionChecker());
}

abstract class Expression {
}

abstract class Import : Expression {
	Module mod;
	this(Module mod) {
		this.mod = mod;
	}
}

abstract class Term : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	Type type;
	this(Type type) {
		this.type = type;
	}

abstract:

	Term substitute(Dictonary!(TypeVariableId, Type) moves);
	Term substitute(Dictonary!(RigidVariableId, Type) moves);
	Term substitute(Dictonary!(StageVariableId, Stage) moves);
	Term substitute(Dictonary!(VariableId, Term) moves);
	Term substitute(Dictonary!(VariableId, VariableId) moves);
	// only for removing symbol forward references
	Term substitute(Dictonary!(SymbolId, Term) moves);
	Term alphaConvert();
	Term reduceMacros();

	Js.JsExpr generateJs(Js.JsScope depend, Extra extra);
	string toStringIndent(uint indent);
}

struct SymbolId {
	size_t raw;
}

abstract class SymbolForwardReference : Term {
	SymbolId id;
	this(Type type, SymbolId id) {
		super(type);
		this.id = id;
	}
}

auto destructure(alias c)(SymbolForwardReference that) {
	with (that)
		return c(type, id);
}

enum Linkage {
	strong,
	weak,
}

abstract class SymbolReference : Term {
	string name;
	SymbolId id;
	Tuple!(Type, Predicate)[] dictonaries;
	this(Type type, string name, SymbolId id, Tuple!(Type, Predicate)[] dictonaries) {
		super(type);
		this.name = name;
		this.id = id;
		this.dictonaries = dictonaries;
	}
}

auto destructure(alias c)(SymbolReference that) {
	with (that)
		return c(type, name, id, dictonaries);
}

struct SymbolValue {
	Term source;
	Linkage linkage;
	string name;
	Tuple!(TypeVariable, Predicate)[] dictonaries;
}

abstract class ExternJs : Term {
	string name;
	Tuple!(Type, Predicate)[] dictonaries;
	this(Type type, string name, Tuple!(Type, Predicate)[] dictonaries) {
		super(type);
		this.name = name;
		this.dictonaries = dictonaries;
	}
}

auto destructure(alias c)(ExternJs that) {
	with (that)
		return c(type, name, dictonaries);
}

struct Argument {
	VariableId id;
	string name;
}

abstract class MacroFunctionLiteral : Term {
	Argument argument;
	Term text;
	this(Type type, Argument argument, Term text) {
		super(type);
		this.argument = argument;
		this.text = text;
	}
}

auto destructure(alias c)(MacroFunctionLiteral that) {
	with (that)
		return c(type, argument, text);
}

struct VariableId {
	size_t raw;
}

abstract class Variable : Term {
	string name;
	VariableId id;
	this(Type type, string name, VariableId id) {
		super(type);
		this.name = name;
		this.id = id;
	}
}

auto destructure(alias c)(Variable that) {
	with (that)
		return c(type, name, id);
}

abstract class VariableDefinition : Term {
	Pattern variable;
	Term value;
	Term last;
	this(Type type, Pattern variable, Term value, Term last) {
		super(type);
		this.variable = variable;
		this.value = value;
		this.last = last;
	}
}

auto destructure(alias c)(VariableDefinition that) {
	with (that)
		return c(type, variable, value, last);
}

abstract class Call : Term {
	Term calle;
	Term argument;
	this(Type type, Term calle, Term argument) {
		super(type);
		this.calle = calle;
		this.argument = argument;
	}
}

auto destructure(alias c)(Call that) {
	with (that)
		return c(type, calle, argument);
}

abstract class MacroCall : Term {
	Term calle;
	Term argument;
	this(Type type, Term calle, Term argument) {
		super(type);
		this.calle = calle;
		this.argument = argument;
	}
}

auto destructure(alias c)(MacroCall that) {
	with (that)
		return c(type, calle, argument);
}

abstract class If : Term {
	Term cond;
	Term yes;
	Term no;
	this(Type type, Term cond, Term yes, Term no) {
		super(type);
		this.cond = cond;
		this.yes = yes;
		this.no = no;
	}
}

auto destructure(alias c)(If that) {
	with (that)
		return c(type, cond, yes, no);
}

abstract class IntLit : Term {
	BigInt value;
	this(Type type, BigInt value) {
		super(type);
		this.value = value;
	}
}

auto destructure(alias c)(IntLit that) {
	with (that)
		return c(type, value);
}

abstract class CharLit : Term {
	dchar value;
	this(Type type, dchar value) {
		super(type);
		this.value = value;
	}
}

auto destructure(alias c)(CharLit that) {
	with (that)
		return c(type, value);
}

abstract class BoolLit : Term {
	bool yes;
	this(Type type, bool yes) {
		super(type);
		this.yes = yes;
	}
}

auto destructure(alias c)(BoolLit that) {
	with (that)
		return c(type, yes);
}

abstract class TupleLit : Term {
	Term[] values;
	this(Type type, Term[] values) {
		super(type);
		this.values = values;
	}
}

auto destructure(alias c)(TupleLit that) {
	with (that)
		return c(type, values);
}

abstract class StringLit : Term {
	string value;
	this(Type type, string value) {
		super(type);
		this.value = value;
	}
}

auto destructure(alias c)(StringLit that) {
	with (that)
		return c(type, value);
}

abstract class ArrayLit : Term {
	Term[] values;
	this(Type type, Term[] values) {
		super(type);
		this.values = values;
	}
}

auto destructure(alias c)(ArrayLit that) {
	with (that)
		return c(type, values);
}

abstract class Requirement : Term {
	Predicate requirement;
	Type context;
	this(Type type, Predicate requirement, Type context) {
		super(type);
		this.requirement = requirement;
		this.context = context;
	}
}

auto destructure(alias c)(Requirement that) {
	with (that)
		return c(type, requirement, context);
}

abstract class Pattern : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	Type type;
	this(Type type) {
		this.type = type;
	}

abstract:
	Pattern substitute(Dictonary!(TypeVariableId, Type) moves);
	Pattern substitute(Dictonary!(RigidVariableId, Type) moves);
	Pattern substitute(Dictonary!(StageVariableId, Stage) moves);
	Pattern substitute(Dictonary!(VariableId, VariableId) moves);
	Js.JsPattern generatePatternMatch(Extra extra);
	Tuple!(Variable, bool)[] orderedBindings();
}

abstract class NamedPattern : Pattern {
	VariableId id;
	string name;
	bool shadow;
	this(Type type, VariableId id, string name, bool shadow) {
		super(type);
		this.id = id;
		this.name = name;
		this.shadow = shadow;
	}
}

auto destructure(alias c)(NamedPattern that) {
	with (that)
		return c(type, id, name, shadow);
}

abstract class TuplePattern : Pattern {
	Pattern[] matches;
	this(Type type, Pattern[] matches) {
		super(type);
		this.matches = matches;
	}
}

auto destructure(alias c)(TuplePattern that) {
	with (that)
		return c(type, matches);
}

enum TypePrecedence {
	zero,
	arrow,
	raw,
	top
}

abstract class TypeScheme : Expression {
abstract:
	TypeScheme substitute(Dictonary!(TypeVariableId, Type) moves);
	Type instantiate(Type delegate(Stage stage, Dictonary!(PredicateId, Predicate), string));

	bool headMatch(Type right);
}

abstract class TypeSchemeForall : TypeScheme {
	TypeVariableId id;
	Stage argumentType;
	Dictonary!(PredicateId, Predicate) qualified;
	string name;
	TypeScheme enclosed;

	this(TypeVariableId id, Stage argumentType, Dictonary!(PredicateId, Predicate) qualified, string name, TypeScheme enclosed) {
		this.id = id;
		this.argumentType = argumentType;
		this.qualified = qualified;
		this.name = name;
		this.enclosed = enclosed;
	}
}

abstract class Type : TypeScheme {
	import codegen.codegen : Extra;
	import Js = jsast;

	Stage type;
	this(Stage type) {
		this.type = type;
	}

	override final string toString() {
		return toStringPrecedence(TypePrecedence.zero);
	}

abstract:

	Set!TypeVariableId freeVariables();
	TypeVariableId[] freeVariablesOrdered();
	Set!RigidVariableId freeRigidVariables();

	override Type substitute(Dictonary!(TypeVariableId, Type) moves);
	Type substitute(Dictonary!(RigidVariableId, Type) moves);
	Type substitute(Dictonary!(StageVariableId, Stage) moves);
	string toStringPrecedence(TypePrecedence);

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

	void checkDispatch(PredicateTypeMatch left, Position, TypeSystem);
	void checkDispatch(PredicateTuple left, Position, TypeSystem);

	bool matchDispatch(TypeMatchEqual left);
	bool matchDispatch(TypeMatchNumber left);
	bool matchDispatch(TypeMatchUnrestricted left);
	bool matchDispatch(TypeMatchCustom left);
	bool matchDispatch(TypeMatchOr left);

	TypeAlgebra[] checkMatchDispatch(TypeMatchEqual left, Position);
	TypeAlgebra[] checkMatchDispatch(TypeMatchNumber left, Position);
	TypeAlgebra[] checkMatchDispatch(TypeMatchUnrestricted left, Position);
	TypeAlgebra[] checkMatchDispatch(TypeMatchCustom left, Position);
	TypeAlgebra[] checkMatchDispatch(TypeMatchOr left, Position);

	bool headMatchDispatch(TypeVariable left);
	bool headMatchDispatch(TypeVariableRigid left);
	bool headMatchDispatch(TypeBool left);
	bool headMatchDispatch(TypeChar left);
	bool headMatchDispatch(TypeInt left);
	bool headMatchDispatch(TypeStruct left);
	bool headMatchDispatch(TypeArray left);
	bool headMatchDispatch(TypeFunction left);
	bool headMatchDispatch(TypeMacro left);
	bool headMatchDispatch(TypePointer left);
	bool headMatchDispatch(TypeOwnPointer left);
	bool headMatchDispatch(TypeOwnArray left);
	bool headMatchDispatch(TypeWorld left);

	Js.JsExpr info(PredicateTypeMatch, Js.JsScope depend, Extra extra);
	Js.JsExpr info(PredicateTuple, Js.JsScope depend, Extra extra);
	Js.JsExpr info(TypeMatchEqual, Js.JsScope depend, Extra extra);
	Js.JsExpr info(TypeMatchNumber, Js.JsScope depend, Extra extra);
	Js.JsExpr info(TypeMatchUnrestricted, Js.JsScope depend, Extra extra);
	Js.JsExpr info(TypeMatchCustom, Js.JsScope depend, Extra extra);
	Js.JsExpr info(TypeMatchOr, Js.JsScope depend, Extra extra);

	Type[] internal();
}

struct RigidContextId {
	size_t raw;
}

struct RigidVariableId {
	size_t raw;
}

abstract class TypeVariableRigid : Type {
	RigidVariableId id;
	string name;
	RigidContextId context;
	this(Stage type, RigidVariableId id, string name, RigidContextId context) {
		super(type);
		this.id = id;
		this.name = name;
		this.context = context;
	}
}

auto destructure(alias c)(TypeVariableRigid that) {
	with (that)
		return c(type, id, name, context);
}

struct TypeVariableId {
	size_t raw;
}

abstract class TypeVariable : Type {
	TypeVariableId id;
	this(Stage type, TypeVariableId id) {
		super(type);
		this.id = id;
	}
}

auto destructure(alias c)(TypeVariable that) {
	with (that)
		return c(type, id);
}

abstract class TypeBool : Type {
	this(Stage type) {
		super(type);
	}
}

auto destructure(alias c)(TypeBool that) {
	with (that)
		return c(type);
}

abstract class TypeChar : Type {
	this(Stage type) {
		super(type);
	}
}

auto destructure(alias c)(TypeChar that) {
	with (that)
		return c(type);
}

abstract class TypeInt : Type {
	uint size;
	bool signed;
	this(Stage type, uint size, bool signed) {
		super(type);
		this.size = size;
		this.signed = signed;
	}
}

auto destructure(alias c)(TypeInt that) {
	with (that)
		return c(type, size, signed);
}

abstract class TypeStruct : Type {
	Type[] values;
	this(Stage type, Type[] values) {
		super(type);
		this.values = values;
	}
}

auto destructure(alias c)(TypeStruct that) {
	with (that)
		return c(type, values);
}

abstract class TypeFunction : Type {
	Type result;
	Type argument;
	this(Stage type, Type result, Type argument) {
		super(type);
		this.result = result;
		this.argument = argument;
	}
}

auto destructure(alias c)(TypeFunction that) {
	with (that)
		return c(type, result, argument);
}

abstract class TypeMacro : Type {
	Type result;
	Type argument;
	this(Stage type, Type result, Type argument) {
		super(type);
		this.result = result;
		this.argument = argument;
	}
}

auto destructure(alias c)(TypeMacro that) {
	with (that)
		return c(type, result, argument);
}

abstract class TypeArray : Type {
	Type value;
	this(Stage type, Type value) {
		super(type);
		this.value = value;
	}
}

auto destructure(alias c)(TypeArray that) {
	with (that)
		return c(type, value);
}

abstract class TypeOwnArray : Type {
	Type value;
	this(Stage type, Type value) {
		super(type);
		this.value = value;
	}
}

auto destructure(alias c)(TypeOwnArray that) {
	with (that)
		return c(type, value);
}

abstract class TypePointer : Type {
	Type value;
	this(Stage type, Type value) {
		super(type);
		this.value = value;
	}
}

auto destructure(alias c)(TypePointer that) {
	with (that)
		return c(type, value);
}

abstract class TypeOwnPointer : Type {
	Type value;
	this(Stage type, Type value) {
		super(type);
		this.value = value;
	}
}

auto destructure(alias c)(TypeOwnPointer that) {
	with (that)
		return c(type, value);
}

abstract class TypeWorld : Type {
	this(Stage type) {
		super(type);
	}
}

auto destructure(alias c)(TypeWorld that) {
	with (that)
		return c(type);
}

abstract class TypeMatch : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;
	import semantic.semantic : Context;

	this() {
	}

abstract:

	bool match(Type);
	TypeAlgebra[] checkMatch(Type right, Position position);
	Js.JsExpr typeInfo(Type type, Js.JsScope depend, Extra extra);
	void validate(Type delegate(Type) base, Context context, Position position);
}

abstract class TypeMatchEqual : TypeMatch {
	this() {
	}
}

abstract class TypeMatchNumber : TypeMatch {
	this() {
	}
}

abstract class TypeMatchUnrestricted : TypeMatch {
	this() {
	}
}

abstract class TypeMatchCustom : TypeMatch {
	TypeScheme pattern;
	Term match;
	this(TypeScheme pattern, Term match) {
		this.pattern = pattern;
		this.match = match;
	}
}

abstract class TypeMatchOr : TypeMatch {
	TypeMatch left;
	TypeMatch right;
	this(TypeMatch left, TypeMatch right) {
		this.left = left;
		this.right = right;
	}
}

enum PredicateNormalId {
	equal,
	number,
	unrestricted
};

struct PredicateTupleId {
	size_t index;
}

struct PredicateCustomId {
	string name;
	size_t index;
}

struct PredicateId {
	Algebraic!(PredicateNormalId, PredicateTupleId, PredicateCustomId) raw;
	this(PredicateNormalId normal) {
		raw = normal;
	}

	this(PredicateTupleId tuple) {
		raw = tuple;
	}

	this(PredicateCustomId custom) {
		raw = custom;
	}
}

abstract class Predicate : Expression {
	import codegen.codegen : Extra;
	import Js = jsast;

	PredicateId id;

	this(PredicateId id) {
		this.id = id;
	}

abstract:

	Set!TypeVariableId freeVariables();
	TypeVariableId[] freeVariablesOrdered();

	Type require(Type variable);

	Predicate substitute(Dictonary!(TypeVariableId, Type) moves);
	Predicate substitute(Dictonary!(RigidVariableId, Type) moves);
	Predicate substitute(Dictonary!(StageVariableId, Stage) moves);
	override string toString();

	void check(Type right, Position, TypeSystem);
	TypeAlgebra[] decompose(Predicate right, Position);

	Js.JsExpr typeInfo(Type type, Js.JsScope depend, Extra extra);
}

abstract class PredicateTypeMatch : Predicate {
	TypeMatch pattern;
	Type delegate(Type) requirement;
	this(PredicateId id, TypeMatch pattern, Type delegate(Type) requirement) {
		super(id);
		this.pattern = pattern;
		this.requirement = requirement;
	}
}

abstract class PredicateTuple : Predicate {
	uint index;
	Type type;
	this(PredicateId id, uint index, Type type) {
		super(id);
		this.index = index;
		this.type = type;
	}
}

auto destructure(alias c)(PredicateTuple that) {
	with (that)
		return c(id, index, type);
}

enum StagePrecedence {
	zero,
	arrow,
	top
}

abstract class Stage : Expression {
	this() {
	}

	override final string toString() {
		return toStringPrecedence(StagePrecedence.zero);
	}

abstract:

	Set!StageVariableId freeVariables();
	Stage substitute(Dictonary!(StageVariableId, Stage) moves);

	string toStringPrecedence(StagePrecedence);

	void unify(Stage right, Position, StageSystem);
	void unifyMatch(StageRuntime left, Position, StageSystem);
	void unifyMatch(StageMacro left, Position, StageSystem);
	void unifyMatch(StageVariable left, Position, StageSystem);
}

struct StageVariableId {
	size_t raw;
}

abstract class StageVariable : Stage {
	StageVariableId id;
	this(StageVariableId id) {
		this.id = id;
	}
}

auto destructure(alias c)(StageVariable that) {
	with (that)
		return c(id);
}

abstract class StageRuntime : Stage {
	this() {
	}
}

auto destructure(alias c)(StageRuntime that) {
	with (that)
		return c();
}

abstract class StageMacro : Stage {
	Stage result;
	Stage argument;
	this(Stage result, Stage argument) {
		this.result = result;
		this.argument = argument;
	}
}

auto destructure(alias c)(StageMacro that) {
	with (that)
		return c(result, argument);
}

abstract class StagePredicateId {
}

abstract class StagePredicate : Expression {
	this() {
	}

abstract:

	StagePredicateId id();
	StagePredicate substitute(Dictonary!(StageVariableId, Stage) moves);
	Set!StageVariableId freeVariables();
	StageAlgebra[] decompose(StagePredicate right, Position);

	void check(Stage right, Position, StageSystem);
}

abstract class TypeAlgebra {
	TypeAlgebra substitute(Dictonary!(TypeVariableId, Type) moves);
	TypeAlgebra substitute(Dictonary!(RigidVariableId, Type) moves);
	Set!TypeVariableId freeVariables();
	void reduce(TypeSystem);

	override string toString();
}

abstract class TypeEquation : TypeAlgebra {
	Type left;
	Type right;
	Position position;
	this(Type left, Type right, Position position) {
		this.left = left;
		this.right = right;
		this.position = position;
	}
}

abstract class TypePredicateCall : TypeAlgebra {
	Predicate predicate;
	Type type;
	Position position;
	this(Predicate predicate, Type type, Position position) {
		this.predicate = predicate;
		this.type = type;
		this.position = position;
	}
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

abstract class StageAlgebra {
abstract:
	StageAlgebra substitute(Dictonary!(StageVariableId, Stage) moves);
	Set!StageVariableId freeVariables();
	void reduce(StageSystem);

	override string toString();
}

abstract class StageEquation : StageAlgebra {
	Stage left;
	Stage right;
	Position position;
	this(Stage left, Stage right, Position position) {
		this.left = left;
		this.right = right;
		this.position = position;
	}
}

abstract class StagePredicateCall : StageAlgebra {
	StagePredicate predicate;
	Stage type;
	Position position;
	this(StagePredicate predicate, Stage type, Position position) {
		this.predicate = predicate;
		this.type = type;
		this.position = position;
	}
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
