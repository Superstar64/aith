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
module semantic.astimpl;

import std.meta;
import std.typecons;
import std.conv;
import std.algorithm;
import std.range;

public import semantic.ast;
import Parser = parser.ast;

import misc.nonstrict;
import misc.getters;
import misc.position;
import misc.container;
import misc.misc;

template make(T) {
	T make(A...)(A args) {
		return new Impl!T(args);
	}
}

mixin template DefaultSpecialize(T) {
	T specialize(Dictonary!(TypeVariableId, Type) moves) {
		return visit!(make!T, a => a.specialize(moves), a => a.specialize(moves), a => a.specialize(moves), a => a)(this);
	}
}

mixin template DefaultMorph(T) {
	mixin DefaultSpecialize!T;
}

// todo remove global state
PredicateId predicateId(T : PredicateNumber)(PredicateNumber predicate) {
	static __gshared value = make!PredicateId();
	return value;
}

PredicateId predicateId(T : PredicateEqual)(PredicateEqual predicate) {
	static __gshared value = make!PredicateId();
	return value;
}

PredicateId predicateId(T : PredicateUnrestricted)(PredicateUnrestricted predicate) {
	static __gshared value = make!PredicateId();
	return value;
}

PredicateId predicateId(T : PredicateTuple)(PredicateTuple predicate) {
	static __gshared PredicateId[int] values;
	if (!(predicate.index in values)) {
		values[predicate.index] = make!PredicateId;
	}
	return values[predicate.index];
}

class Impl(T) : T {
	mixin Getters!T;
}

class Impl(T : TypeVariableId) : T {
	mixin Getters!T;
	override string toString() {
		if (name == "") {
			return this.castTo!(void*)
				.to!string;
		} else {
			return name;
		}
	}
}

class Impl(T : Pattern) : T {
	mixin Getters!T;
	mixin DefaultMorph!T;
	import Js = jsast;
	import codegen.codegen : Extra, generatePatternMatchImpl;
	import semantic.semantic;

	Js.JsPattern generatePatternMatch(Extra extra) {
		return generatePatternMatchImpl(this, extra);
	}

	void removeBindings(Context context, Position position) {
		removeBindingsImpl(this, context, position);
	}
}

class Impl(T : Term) : T {
	mixin Getters!T;
	mixin DefaultMorph!T;

	import Js = jsast;
	import codegen.codegen : Extra, generateJsImpl, generateSymbolImpl;

	Js.JsExpr generateJs(Js.JsScope depend, Extra extra) {
		return generateJsImpl(this, depend, extra);
	}

	static if (is(T : Symbol)) {
		Dictonary!(Tuple!(SymbolId, TypeHash), Symbol) dependants() {
			return visit!(mergeMapsLeft, a => a.symbols, a => emptyMap!(Tuple!(SymbolId, TypeHash), Symbol), a => emptyMap!(Tuple!(SymbolId, TypeHash), Symbol), a => emptyMap!(Tuple!(SymbolId, TypeHash), Symbol))(this);
		}

		Dictonary!(Tuple!(SymbolId, TypeHash), Symbol) symbols() {
			return [tuple(id, type.typeHash): this.convert!Symbol].fromAALiteral;
		}

		Js.JsExpr generateSymbol(Js.JsScope depend, Extra extra) {
			return generateSymbolImpl(this, depend, extra);
		}
	} else {
		Dictonary!(Tuple!(SymbolId, TypeHash), Symbol) symbols() {
			return visit!(mergeMapsLeft, a => a.symbols, a => emptyMap!(Tuple!(SymbolId, TypeHash), Symbol), a => emptyMap!(Tuple!(SymbolId, TypeHash), Symbol), a => emptyMap!(Tuple!(SymbolId, TypeHash), Symbol))(this);
		}
	}
}

class Impl(T : Type) : T {
	mixin Getters!T;

	override string toString() {
		return toStringImpl(this);
	}

	Dictonary!(TypeVariableId, Type) typeMatch(Type right, Position position) {
		return right.typeMatchDispatch(this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeVariable left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeBool left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeChar left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeInt left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeStruct left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeArray left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeFunction left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypePointer left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeOwnPointer left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeOwnArray left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) typeMatchDispatch(TypeWorld left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Dictonary!(TypeVariableId, Type) predicateInstantiateDispatch(PredicateEqual left, Dictonary!(TypeVariableId, Type) current, Position position) {
		return predicateInstantiateImpl(left, this, current, position);
	}

	Dictonary!(TypeVariableId, Type) predicateInstantiateDispatch(PredicateNumber left, Dictonary!(TypeVariableId, Type) current, Position position) {
		return predicateInstantiateImpl(left, this, current, position);
	}

	Dictonary!(TypeVariableId, Type) predicateInstantiateDispatch(PredicateTuple left, Dictonary!(TypeVariableId, Type) current, Position position) {
		return predicateInstantiateImpl(left, this, current, position);
	}

	Dictonary!(TypeVariableId, Type) predicateInstantiateDispatch(PredicateUnrestricted left, Dictonary!(TypeVariableId, Type) current, Position position) {
		return predicateInstantiateImpl(left, this, current, position);
	}

	static if (is(T : TypeVariable)) {
		override string name() {
			return id.name;
		}

		override Type specialize(Dictonary!(TypeVariableId, Type) moves) {
			if (id in moves) {
				return moves[id];
			} else {
				return make!TypeVariable(id, constraints.mapValues!(a => a.specialize(moves)), rigidity);
			}
		}

		Dictonary!(TypeVariableId, TypeVariable) freeVariables() {
			auto extra = .freeVariables(constraints.byValue);
			return mergeMapsLeft(extra, [id: this.convert!TypeVariable].fromAALiteral);
		}

		import Js = jsast;
		import codegen.codegen : Extra, mangleImpl, compareInfoImpl;

		Js.JsExpr compareInfo(Extra extra) {
			assert(0);
		}

		string mangle() {
			assert(0);
		}
	} else {
		mixin DefaultMorph!T;

		Dictonary!(TypeVariableId, TypeVariable) freeVariables() {
			return visit!(.freeVariables, a => a, a => a, a => { static assert(0); }, a => emptyArray!Type)(this);
		}

		import Js = jsast;
		import codegen.codegen : Extra, mangleImpl, compareInfoImpl;

		Js.JsExpr compareInfo(Extra extra) {
			return compareInfoImpl(this, extra);
		}

		string mangle() {
			return mangleImpl(this);
		}
	}
}

class Impl(T : Predicate) : T {
	mixin Getters!T;

	override PredicateId id() {
		return predicateId!T(this);
	}

	Dictonary!(TypeVariableId, TypeVariable) freeVariables() {
		return visit!(.freeVariables, a => a, a => a, a => { static assert(0); }, a => emptyArray!Type)(this);
	}

	mixin DefaultSpecialize!T;

	Dictonary!(TypeVariableId, Type) predicateInstantiate(Type right, Dictonary!(TypeVariableId, Type) current, Position position) {
		return right.predicateInstantiateDispatch(this, current, position);
	}

	Dictonary!(TypeVariableId, Type) predicateMatch(Predicate right0, Dictonary!(TypeVariableId, Type) current, Position position) {
		auto right1 = right0.castTo!(typeof(this));
		assert(right1);
		return predicateMatchImpl(this, right1, current, position);
	}

	override string toString() {
		return toStringImpl(this);
	}
}

// visitors, where f is other expressions, p is pattern matches, t are types, and i is for misc data
auto visit(alias construct, alias f, alias p, alias t, alias i, T : NamedPattern)(T that) {
	with (that)
		return construct(t(type), f(argument));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TuplePattern)(T that) {
	with (that)
		return construct(t(type), f(matches));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : FunctionLiteral)(T that) {
	with (that)
		return construct(t(type), i(name), i(linkage), i(id), p(argument), f(text));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : Variable)(T that) {
	with (that)
		return construct(t(type), i(name), i(id));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : VariableDefinition)(T that) {
	with (that)
		return construct(t(type), p(variable), f(value), f(last));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : Desugar!name, string name)(T that) {
	with (that)
		return construct(t(type));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : DesugarContext!name, string name)(T that) {
	with (that)
		return construct(t(type), t(context));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : IntLit)(T that) {
	with (that)
		return construct(t(type), i(value));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : CharLit)(T that) {
	with (that)
		return construct(t(type), i(value));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : BoolLit)(T that) {
	with (that)
		return construct(t(type), i(yes));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TupleLit)(T that) {
	with (that)
		return construct(t(type), f(values));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : If)(T that) {
	with (that)
		return construct(t(type), f(cond), f(yes), f(no));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : CastInteger)(T that) {
	with (that)
		return construct(t(type), t(contextWanted), t(contextInput));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TupleIndex)(T that) {
	with (that)
		return construct(t(type), i(index));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TupleIndexAddress)(T that) {
	with (that)
		return construct(t(type), i(index), t(context));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : Call)(T that) {
	with (that)
		return construct(t(type), f(calle), f(argument));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : StringLit)(T that) {
	with (that)
		return construct(t(type), i(value));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : ArrayLit)(T that) {
	with (that)
		return construct(t(type), f(values));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : ExternJs)(T that) {
	with (that)
		return construct(t(type), i(name));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeBool)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeChar)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeInt)(T that) {
	with (that)
		return construct(i(size), i(signed));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeStruct)(T that) {
	with (that)
		return construct(f(values));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeArray)(T that) {
	with (that)
		return construct(f(array));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeFunction)(T that) {
	with (that)
		return construct(f(result), f(argument));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypePointer)(T that) {
	with (that)
		return construct(f(value));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeOwnPointer)(T that) {
	with (that)
		return construct(f(value));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeOwnArray)(T that) {
	with (that)
		return construct(f(array));
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : TypeWorld)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : PredicateEqual)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : PredicateNumber)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : PredicateUnrestricted)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, alias p, alias t, alias i, T : PredicateTuple)(T that) {
	with (that)
		return construct(i(index), f(type));
}

string toStringImpl(TypeBool that) {
	return "boolean";
}

string toStringImpl(TypeChar that) {
	return "character";
}

string toStringImpl(TypeInt that) {
	return (that.signed ? "integer " : "natural ") ~ that.size.to!string;
}

string toStringImpl(TypeStruct that) {
	return "(&" ~ that.values
		.map!(a => a.toString ~ ",")
		.joiner
		.array
		.to!string ~ "&)";
}

string toStringImpl(TypeArray that) {
	return that.array.toString ~ "[*]";
}

string toStringImpl(TypeFunction that) {
	return that.argument.toString ~ " -> " ~ that.result.toString;
}

string toStringImpl(TypePointer that) {
	return that.value.toString ~ "(*)";
}

string toStringImpl(TypeOwnPointer that) {
	return that.value.toString ~ "(!)";
}

string toStringImpl(TypeOwnArray that) {
	return that.array.toString ~ "[!]";
}

string toStringImpl(TypeWorld that) {
	return "world";
}

string toStringImpl(TypeVariable that) {
	string result;
	if (that.rigidity.length > 0) {
		result ~= "<rigid>";
	}
	result ~= that.id.to!string;
	if (that.constraints.length > 0) {
		result ~= " extends (";
		result ~= that.constraints.byValue.map!(a => a.to!string()).joiner(",").array.to!string;
		result ~= ")";
	}
	return result;
}

string toStringImpl(PredicateEqual that) {
	return "equal";
}

string toStringImpl(PredicateNumber that) {
	return "number";
}

string toStringImpl(PredicateUnrestricted that) {
	return "unrestricted";
}

string toStringImpl(PredicateTuple that) {
	return that.index.to!string ~ " : " ~ that.type.to!string;
}

struct Equivalence {
	Type left;
	Type right;
	Position position;

	this(Type left, Type right, Position position) {
		this.left = left;
		this.right = right;
		this.position = position;
		assert(left);
		assert(right);
	}

	Dictonary!(TypeVariableId, TypeVariable) freeVariables() {
		return .freeVariables(left, right);
	}

	Equivalence specialize(Dictonary!(TypeVariableId, Type) moves) {
		return Equivalence(left.specialize(moves), right.specialize(moves), position);
	}

	string toString() {
		return left.to!string ~ " ~ " ~ right.to!string;
	}
}

Dictonary!(TypeVariableId, TypeVariable) substitutionRange(Dictonary!(TypeVariableId, Type) substitution) {
	return substitution.byValue.freeVariables;
}

Dictonary!(TypeVariableId, Type) freshSubstitution(T...)(T items) {
	auto variables = freeVariables(items);
	Dictonary!(TypeVariableId, Type) result;
	foreach (id, variable; variables.range) {
		result[id] = make!TypeVariable(make!TypeVariableId(id.name), variable.constraints, variable.rigidity);
	}
	foreach (id, variable; result.range) {
		result = result.insert(id, variable.specialize(result));
	}
	return result;
}

Dictonary!(TypeVariableId, Type) freshFlexibleSubstitution(T...)(T items) {
	auto variables = freeVariables(items);
	Dictonary!(TypeVariableId, Type) result;
	foreach (id, variable; variables.range) {
		result[id] = make!TypeVariable(make!TypeVariableId(id.name), variable.constraints, emptyMap!(RigidContext, RigidVariable));
	}
	foreach (id, variable; result.range) {
		result = result.insert(id, variable.specialize(result));
	}
	return result;
}

Dictonary!(TypeVariableId, Type) removeTemporaries(Dictonary!(TypeVariableId, TypeVariable) temporaries, Dictonary!(TypeVariableId, Type) future) {
	Dictonary!(TypeVariableId, Type) result;
	foreach (variable, type; future.range) {
		if (!(variable in temporaries)) {
			result[variable] = type;
		}
	}
	return result;
}

void assertCombineProperties(Dictonary!(TypeVariableId, Type) current, Dictonary!(TypeVariableId, Type) future) {
	auto currentDomain = current.byKey;
	auto futureRange = future.substitutionRange;
	foreach (variable; currentDomain) {
		assert(!(variable in futureRange));
	}
}

Dictonary!(TypeVariableId, Type) combineSubstitutions(Dictonary!(TypeVariableId, Type) current0, Dictonary!(TypeVariableId, Type) future0) {
	assertCombineProperties(current0, future0);
	auto temporaries = current0.substitutionRange;
	auto current1 = current0.specialize(future0);
	auto future1 = removeTemporaries(temporaries, future0);
	return mergeMapsUnique(current1, future1);
}

Dictonary!(TypeVariableId, Type) continueSubsitution(T)(Dictonary!(TypeVariableId, Type) current, T equation) {
	auto future = typeMatch(equation.specialize(current));
	auto result = combineSubstitutions(current, future);
	return result;
}

void assertProperties(Dictonary!(TypeVariableId, TypeVariable) input, Dictonary!(TypeVariableId, Type) solution) {
	foreach (variable; input.byKey) {
		auto range = solution.substitutionRange;
		assert(!(variable in range), variable.to!string ~ " found in " ~ range.to!string);
	}
	foreach (variable; input.byKey) {
		assert(variable in solution);
	}
	foreach (variable, type; solution.range) {
		assert(variable in input);
	}
}

// no type variables from any of the equations should appear in range of result
// all type variables from all of the equations must appear in the domain of the result
Dictonary!(TypeVariableId, Type) typeMatch(Equivalence[] equations) {
	if (equations.empty) {
		return emptyMap!(TypeVariableId, Type);
	}
	auto head = equations.front;
	auto remainder = equations.dropOne;

	auto current = typeMatch(head);
	auto result = continueSubsitution(current, remainder);

	version (assert) {
		auto input = equations.freeVariables;
		assertProperties(input, result);
	}

	return result;
}

Dictonary!(TypeVariableId, Type) typeMatch(Equivalence equation) {
	return typeMatch(equation.left, equation.right, equation.position);
}

Dictonary!(TypeVariableId, Type) typeMatch(Type left, Type right, Position position) {
	return left.typeMatch(right, position);
}

Dictonary!(TypeVariableId, Type) typeMatchImpl(T1, T2)(T1 left, T2 right, Position position) {
	auto result = typeMatchImplReal(left, right, position);
	version (assert) {
		auto input = freeVariables(left, right);
		assertProperties(input, result);
	}
	return result;
}

bool checkRigidity(TypeVariable left, TypeVariable right) {
	auto leftRigidity = left.rigidity.keys;
	auto rightRigidity = right.rigidity.keys;
	auto leftConstraints = left.constraints.keys;
	auto rightConstraints = right.constraints.keys;
	auto common = intersectSets(leftRigidity, rightRigidity);
	auto valid = common.range.map!(context => left.rigidity[context] is right.rigidity[context]).all;
	if (left.rigidity.length != 0) {
		valid &= isSubSet(rightConstraints, leftConstraints);
	}
	if (right.rigidity.length != 0) {
		valid &= isSubSet(leftConstraints, rightConstraints);
	}
	return valid;
}

Tuple!(Dictonary!(PredicateId, Predicate), Dictonary!(TypeVariableId, Type)) matchConstraints(Dictonary!(PredicateId, Predicate) left, Dictonary!(PredicateId, Predicate) right, Position position) {
	auto fresh = freshSubstitution(left, right);
	auto clashing = intersectMaps(left, right);
	auto result = clashing.byValue.fold!((current, pair) => pair[0].predicateMatch(pair[1], current, position))(fresh);
	auto total = mergeMapsLeft(left, right).specialize(result);
	return tuple(total, result);
}

//the heart of the compiler

// no type variables from left or right, should appear in the range of the result
// all type variables from left or right should in domain of result
Dictonary!(TypeVariableId, Type) typeMatchImplReal(T1, T2)(T1 left, T2 right, Position position) {
	static if (is(T1 : TypeVariable) && is(T2 : TypeVariable)) {
		if (checkRigidity(left, right)) {
			auto matched = matchConstraints(left.constraints, right.constraints, position);
			auto total = matched[0];
			auto result = matched[1];

			auto rigid = mergeMapsLeft(left.rigidity, right.rigidity);
			auto joined = make!TypeVariable(make!TypeVariableId(""), total, rigid);
			return mergeMapsLeft([left.id: joined.convert!Type, right.id: joined.convert!Type].fromAALiteral, result);
		}
	} else static if (is(T1 : TypeVariable) && !is(T2 : TypeVariable)) {
		if (left.rigidity.length == 0) {
			occuranceCheck(left, right, position);
			return qualifiedInstantiate(left, right, position);
		}
	} else static if (!is(T1 : TypeVariable) && is(T2 : TypeVariable)) {
		if (right.rigidity.length == 0) {
			occuranceCheck(right, left, position);
			return qualifiedInstantiate(right, left, position);
		}
	} else static if (is(T1 : TypeBool) && is(T2 : TypeBool)) {
		return emptyMap!(TypeVariableId, Type);
	} else static if (is(T1 : TypeChar) && is(T2 : TypeChar)) {
		return emptyMap!(TypeVariableId, Type);
	} else static if (is(T1 : TypeInt) && is(T2 : TypeInt)) {
		if (left.size == right.size && left.signed == right.signed) {
			return emptyMap!(TypeVariableId, Type);
		}
	} else static if (is(T1 : TypeStruct) && is(T2 : TypeStruct)) {
		if (left.values.length == right.values.length) {
			return zip(left.values, right.values).map!(a => Equivalence(a[0], a[1], position)).array.typeMatch;
		}
	} else static if (is(T1 : TypeArray) && is(T2 : TypeArray)) {
		return typeMatch(left.array, right.array, position);
	} else static if (is(T1 : TypeFunction) && is(T2 : TypeFunction)) {
		return only(Equivalence(left.result, right.result, position), Equivalence(left.argument, right.argument, position)).array.typeMatch;
	} else static if (is(T1 : TypePointer) && is(T2 : TypePointer)) {
		return typeMatch(left.value, right.value, position);
	} else static if (is(T1 : TypeOwnPointer) && is(T2 : TypeOwnPointer)) {
		return typeMatch(left.value, right.value, position);
	} else static if (is(T1 : TypeOwnArray) && is(T2 : TypeOwnArray)) {
		return typeMatch(left.array, right.array, position);
	} else static if (is(T1 : TypeWorld) && is(T2 : TypeWorld)) {
		return emptyMap!(TypeVariableId, Type);
	}

	error("Can't match " ~ left.toString ~ " to " ~ right.toString, position);
	assert(0);
}

void occuranceCheck(TypeVariable qualified, Type type, Position position) {
	if (qualified.id in type.freeVariables) {
		error("Recursive use of variable " ~ qualified.to!string ~ " in " ~ type.to!string, position);
	}
}

Dictonary!(TypeVariableId, Type) qualifiedInstantiate(TypeVariable qualified, Type type, Position position) {
	auto fresh = freshSubstitution(type, qualified.constraints);
	auto result = qualified.constraints.byValue.fold!((current, constraint) => predicateInstantiate(constraint, type, current, position))(fresh);
	result[qualified.id] = type.specialize(result);
	version (assert) {
		auto input = freeVariables(qualified, type);
		assertProperties(input, result);
	}
	return result;
}

Dictonary!(TypeVariableId, Type) predicateInstantiate(Predicate predicate, Type type, Dictonary!(TypeVariableId, Type) current, Position position) {
	return predicate.predicateInstantiate(type, current, position);
}

Dictonary!(TypeVariableId, Type) predicateInstantiateImpl(C, T)(C constraint, T type, Dictonary!(TypeVariableId, Type) current, Position position) {
	static if (is(C : PredicateEqual)) {
		static if (is(T : TypeBool)) {
			return current;
		} else static if (is(T : TypeChar)) {
			return current;
		} else static if (is(T : TypeInt)) {
			return current;
		} else static if (is(T : TypeStruct)) {
			Dictonary!(TypeVariableId, TypeVariable) temporaries;
			Predicate predicate = make!PredicateEqual();
			foreach (subType; type.values) {
				auto fresh = make!TypeVariable(make!TypeVariableId(""), [predicate.id: predicate].fromAALiteral, emptyMap!(RigidContext, RigidVariable));
				temporaries[fresh.id] = fresh;
				current = continueSubsitution(current, Equivalence(subType, fresh, position));
			}
			return removeTemporaries(temporaries, current);
		} else static if (is(T : TypeArray)) {
			Dictonary!(TypeVariableId, TypeVariable) temporaries;
			Predicate predicate = make!PredicateEqual();
			auto fresh = make!TypeVariable(make!TypeVariableId(""), [predicate.id: predicate].fromAALiteral, emptyMap!(RigidContext, RigidVariable));
			temporaries[fresh.id] = fresh;
			current = continueSubsitution(current, Equivalence(type.array, fresh, position));
			return removeTemporaries(temporaries, current);
		} else static if (is(T : TypePointer)) {
			return current;
		}
	} else static if (is(C : PredicateNumber) && is(T : TypeInt)) {
		return current;
	} else static if (is(C : PredicateTuple) && is(T : TypeStruct)) {
		if (constraint.index < type.values.length) {
			return continueSubsitution(current, Equivalence(constraint.type, type.values[constraint.index], position));
		}
	} else static if (is(C : PredicateUnrestricted)) {
		static if (is(T : TypeBool)) {
			return current;
		} else static if (is(T : TypeChar)) {
			return current;
		} else static if (is(T : TypeInt)) {
			return current;
		} else static if (is(T : TypeStruct)) {
			Dictonary!(TypeVariableId, TypeVariable) temporaries;
			Predicate predicate = make!PredicateUnrestricted();
			foreach (subType; type.values) {
				auto fresh = make!TypeVariable(make!TypeVariableId(""), [predicate.id: predicate].fromAALiteral, emptyMap!(RigidContext, RigidVariable));
				temporaries[fresh.id] = fresh;
				current = continueSubsitution(current, Equivalence(subType, fresh, position));
			}
			return removeTemporaries(temporaries, current);
		} else static if (is(T : TypeArray)) {
			return current;
		} else static if (is(T : TypePointer)) {
			return current;
		} else static if (is(T : TypeFunction)) {
			return current;
		}
	}
	error("Can't match constraint " ~ constraint.toString ~ " to " ~ type.toString, position);
	assert(0);
}

Dictonary!(TypeVariableId, Type) predicateMatchImpl(C)(C left, C right, Dictonary!(TypeVariableId, Type) current, Position position) {
	static if (is(C : PredicateEqual)) {
		return current;
	} else static if (is(C : PredicateNumber)) {
		return current;
	} else static if (is(C : PredicateTuple)) {
		assert(left.index == right.index);
		return continueSubsitution(current, Equivalence(left.type, right.type, position));
	} else static if (is(C : PredicateUnrestricted)) {
		return current;
	} else {
		static assert(0);
	}
}

Dictonary!(TypeVariableId, TypeVariable) freeVariables(T)(T item) if (is(T : Type) || is(T : Predicate)) {
	return item.freeVariables;
}

Dictonary!(TypeVariableId, TypeVariable) freeVariables(R)(R data) if (isInputRange!R) {
	return data.map!(a => a.freeVariables)
		.fold!mergeMapsLeft(emptyMap!(TypeVariableId, TypeVariable));
}

Dictonary!(TypeVariableId, TypeVariable) freeVariables(T...)(T arguments) if (T.length > 1) {
	return mergeMapsLeft(arguments[0 .. $ - 1].freeVariables, arguments[$ - 1].freeVariables);
}

Dictonary!(TypeVariableId, TypeVariable) freeVariables(K, V)(Dictonary!(K, V) data) {
	return data.byValue.freeVariables;
}

Dictonary!(TypeVariableId, TypeVariable) freeVariables() {
	return emptyMap!(TypeVariableId, TypeVariable);
}

auto specialize(T)(T[] data, Dictonary!(TypeVariableId, Type) moves) {
	return data.map!(a => a.specialize(moves)).array;
}

auto specialize(K, V)(Dictonary!(K, V) data, Dictonary!(TypeVariableId, Type) moves) {
	return data.mapValues!(a => a.specialize(moves));
}

auto specialize(T)(Lazy!T data, Dictonary!(TypeVariableId, Type) moves) {
	return defer(() => data.get.specialize(moves));
}

auto symbols(T)(Lazy!T data) {
	return data.get.symbols;
}

auto symbols(T)(T[] data) {
	return data.map!(a => a.symbols)
		.fold!mergeMapsLeft(emptyMap!(Tuple!(SymbolId, TypeHash), Symbol));
}

auto toRuntime(T)(T[] data) {
	return data.map!(a => a.toRuntime()).array;
}

auto toRuntime(T)(Lazy!T data) {
	return defer(() => data.get.toRuntime);
}
