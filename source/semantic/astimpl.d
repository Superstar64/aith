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

import genericast;

public import semantic.ast;
static import Codegen = codegen.astimpl;
static import Parser = parser.ast;

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

mixin template DefaultCast() {
	Expression castToExpression() {
		return cast(Expression) this;
	}

	Symbol castToSymbol() {
		return cast(Symbol) this;
	}

	Type castToType() {
		return cast(Type) this;
	}

	Import castToImport() {
		return cast(Import) this;
	}
}

mixin template DefaultSpecialize(T) {
	T specialize(Type[TypeVariableId] moves) {
		return visit!(make!T, a => a.specialize(moves))(this);
	}
}

mixin template DefaultMorph(T) {
	mixin DefaultSpecialize!T;

	RuntimeType!T toRuntime() {
		return visit!(Codegen.make!(RuntimeType!T), a => a.toRuntime())(this);
	}
}

PredicateId predicateId(T : PredicateNumber)(PredicateNumber predicate) {
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
	mixin DefaultCast;
}

class Impl(T : TypeVariableId) : T {
	mixin Getters!T;
	override string toString() {
		if (name == "") {
			return (cast(void*) this).to!string;
		} else {
			return name;
		}
	}
}

class Impl(T : Pattern) : T {
	mixin Getters!T;
	mixin DefaultMorph!T;
	mixin DefaultCast;
}

class Impl(T : Expression) : T {
	mixin Getters!T;
	mixin DefaultMorph!T;
	mixin DefaultCast;
}

class Impl(T : Type) : T {
	mixin Getters!T;

	TypeVariable[TypeVariableId] freeVariables() {
		return unknownImpl(this);
	}

	mixin DefaultCast;

	override string toString() {
		return toStringImpl(this);
	}

	Type[TypeVariableId] typeMatch(Type right, Position position) {
		return right.typeMatchDispatch(this, position);
	}

	Type[TypeVariableId] typeMatchDispatch(TypeVariable left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Type[TypeVariableId] typeMatchDispatch(TypeBool left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Type[TypeVariableId] typeMatchDispatch(TypeChar left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Type[TypeVariableId] typeMatchDispatch(TypeInt left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Type[TypeVariableId] typeMatchDispatch(TypeStruct left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Type[TypeVariableId] typeMatchDispatch(TypeArray left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Type[TypeVariableId] typeMatchDispatch(TypeFunction left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Type[TypeVariableId] typeMatchDispatch(TypePointer left, Position position) {
		return typeMatchImpl(left, this, position);
	}

	Equivalence[] predicateInstantiateDispatch(PredicateNumber left, Position position) {
		return predicateInstantiateImpl(left, this, position);
	}

	Equivalence[] predicateInstantiateDispatch(PredicateTuple left, Position position) {
		return predicateInstantiateImpl(left, this, position);
	}

	static if (is(T : TypeVariable)) {
		override string name() {
			return id.name;
		}

		override Type specialize(Type[TypeVariableId] moves) {
			if (id in moves) {
				return moves[id];
			} else {
				return make!TypeVariable(id, constraints.mapValues!(a => a.specialize(moves)), rigidity);
			}
		}

		override Codegen.Type toRuntime() {
			assert(0);
		}
	} else {
		mixin DefaultMorph!T;
	}
}

class Impl(T : Predicate) : T {
	mixin Getters!T;

	override PredicateId id() {
		return predicateId!T(this);
	}

	TypeVariable[TypeVariableId] freeVariables() {
		return unknownImpl(this);
	}

	mixin DefaultSpecialize!T;
	mixin DefaultCast;

	Equivalence[] predicateInstantiate(Type right, Position position) {
		return right.predicateInstantiateDispatch(this, position);
	}

	Equivalence[] predicateMatch(Predicate right0, Position position) {
		auto right1 = cast(typeof(this))(right0);
		assert(right1);
		return predicateMatchImpl(this, right1, position);
	}

	override string toString() {
		return toStringImpl(this);
	}
}

auto visit(alias construct, alias f, T : NamedPattern)(T that) {
	with (that)
		return construct(f(type), f(argument));
}

auto visit(alias construct, alias f, T : TuplePattern)(T that) {
	with (that)
		return construct(f(type), f(matches));
}

auto visit(alias construct, alias f, T : FunctionLiteral)(T that) {
	with (that)
		return construct(f(type), name, strong, id, f(argument), f(text));
}

auto visit(alias construct, alias f, T : Variable)(T that) {
	with (that)
		return construct(f(type), name, id);
}

auto visit(alias construct, alias f, T : VariableDef)(T that) {
	with (that)
		return construct(f(type), f(variable), f(value), f(last));
}

auto visit(alias construct, alias f, T : IntLit)(T that) {
	with (that)
		return construct(f(type), value);
}

auto visit(alias construct, alias f, T : CharLit)(T that) {
	with (that)
		return construct(f(type), value);
}

auto visit(alias construct, alias f, T : BoolLit)(T that) {
	with (that)
		return construct(f(type), yes);
}

auto visit(alias construct, alias f, T : TupleLit)(T that) {
	with (that)
		return construct(f(type), f(values));
}

auto visit(alias construct, alias f, T : If)(T that) {
	with (that)
		return construct(f(type), f(cond), f(yes), f(no));
}

auto visit(alias construct, alias f, T : While)(T that) {
	with (that)
		return construct(f(type), f(cond), f(state));
}

auto visit(alias construct, alias f, T : New)(T that) {
	with (that)
		return construct(f(type), f(value));
}

auto visit(alias construct, alias f, T : NewArray)(T that) {
	with (that)
		return construct(f(type), f(length), f(value));
}

auto visit(alias construct, alias f, T : CastInteger)(T that) {
	with (that)
		return construct(f(type), f(value));
}

auto visit(alias construct, alias f, T : Length)(T that) {
	with (that)
		return construct(f(type));
}

auto visit(alias construct, alias f, T : Index)(T that) {
	with (that)
		return construct(f(type), f(array), f(index));
}

auto visit(alias construct, alias f, T : IndexAddress)(T that) {
	with (that)
		return construct(f(type), f(array), f(index));
}

auto visit(alias construct, alias f, T : TupleIndex)(T that) {
	with (that)
		return construct(f(type), f(tuple), index);
}

auto visit(alias construct, alias f, T : TupleIndexAddress)(T that) {
	with (that)
		return construct(f(type), f(tuple), index);
}

auto visit(alias construct, alias f, T : Call)(T that) {
	with (that)
		return construct(f(type), f(calle), f(argument));
}

auto visit(alias construct, alias f, T : Slice)(T that) {
	with (that)
		return construct(f(type), f(array), f(left), f(right));
}

auto visit(alias construct, alias f, T : Binary!op, string op)(T that) {
	with (that)
		return construct(f(type), f(left), f(right));
}

auto visit(alias construct, alias f, T : Prefix!op, string op)(T that) {
	with (that)
		return construct(f(type), f(value));
}

auto visit(alias construct, alias f, T : Deref)(T that) {
	with (that)
		return construct(f(type), f(value));
}

auto visit(alias construct, alias f, T : Scope)(T that) {
	with (that)
		return construct(f(type), f(pass), f(last));
}

auto visit(alias construct, alias f, T : Assign)(T that) {
	with (that)
		return construct(f(type), f(left), f(right));
}

auto visit(alias construct, alias f, T : StringLit)(T that) {
	with (that)
		return construct(f(type), value);
}

auto visit(alias construct, alias f, T : ArrayLit)(T that) {
	with (that)
		return construct(f(type), f(values));
}

auto visit(alias construct, alias f, T : ExternJs)(T that) {
	with (that)
		return construct(f(type), name);
}

auto visit(alias construct, alias f, T : TypeBool)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, T : TypeChar)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, T : TypeInt)(T that) {
	with (that)
		return construct(size, signed);
}

auto visit(alias construct, alias f, T : TypeStruct)(T that) {
	with (that)
		return construct(f(values));
}

auto visit(alias construct, alias f, T : TypeArray)(T that) {
	with (that)
		return construct(f(array));
}

auto visit(alias construct, alias f, T : TypeFunction)(T that) {
	with (that)
		return construct(f(result), f(argument));
}

auto visit(alias construct, alias f, T : TypePointer)(T that) {
	with (that)
		return construct(f(value));
}

auto visit(alias construct, alias f, T : PredicateNumber)(T that) {
	with (that)
		return construct();
}

auto visit(alias construct, alias f, T : PredicateTuple)(T that) {
	with (that)
		return construct(index, f(type));
}

TypeVariable[TypeVariableId] unknownImpl(TypeBool that) {
	return null;
}

TypeVariable[TypeVariableId] unknownImpl(TypeChar that) {
	return null;
}

TypeVariable[TypeVariableId] unknownImpl(TypeInt that) {
	return null;
}

TypeVariable[TypeVariableId] unknownImpl(TypeStruct that) {
	return that.values.freeVariables;
}

TypeVariable[TypeVariableId] unknownImpl(TypeArray that) {
	return that.array.freeVariables;
}

TypeVariable[TypeVariableId] unknownImpl(TypeFunction that) {
	return freeVariables(that.result, that.argument);
}

TypeVariable[TypeVariableId] unknownImpl(TypePointer that) {
	return that.value.freeVariables;
}

TypeVariable[TypeVariableId] unknownImpl(TypeVariable that) {
	auto extra = that.constraints.byValue.freeVariables;
	return mergeMapsLeft(extra, [that.id: that]);
}

TypeVariable[TypeVariableId] unknownImpl(PredicateNumber that) {
	return null;
}

TypeVariable[TypeVariableId] unknownImpl(PredicateTuple that) {
	return that.type.freeVariables;
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
	return "(" ~ that.values
		.map!(a => a.toString ~ ",")
		.joiner
		.array
		.to!string ~ ")";
}

string toStringImpl(TypeArray that) {
	return that.array.toString() ~ "[]";
}

string toStringImpl(TypeFunction that) {
	return that.argument.toString ~ "->" ~ that.result.toString;
}

string toStringImpl(TypePointer that) {
	return that.value.toString() ~ "(*)";
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

string toStringImpl(PredicateNumber that) {
	return "number";
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

	TypeVariable[TypeVariableId] freeVariables() {
		return .freeVariables(left, right);
	}

	Equivalence specialize(Type[TypeVariableId] moves) {
		return Equivalence(left.specialize(moves), right.specialize(moves), position);
	}

	string toString() {
		return left.to!string ~ " ~ " ~ right.to!string;
	}
}

TypeVariable[TypeVariableId] substitutionRange(Type[TypeVariableId] substitution) {
	return substitution.byValue.freeVariables;
}

Type[TypeVariableId] freshSubstitution(T...)(T items) {
	auto variables = freeVariables(items);
	Type[TypeVariableId] result;
	foreach (id, variable; variables) {
		result[id] = make!TypeVariable(make!TypeVariableId(id.name), variable.constraints, variable.rigidity);
	}
	foreach (ref variable; result) {
		variable = variable.specialize(result);
	}
	return result;
}

Type[TypeVariableId] freshFlexibleSubstitution(T...)(T items) {
	auto variables = freeVariables(items);
	Type[TypeVariableId] result;
	foreach (id, variable; variables) {
		result[id] = make!TypeVariable(make!TypeVariableId(id.name), variable.constraints, null);
	}
	foreach (ref variable; result) {
		variable = variable.specialize(result);
	}
	return result;
}

Type[TypeVariableId] removeTemporaries(TypeVariable[TypeVariableId] temporaries, Type[TypeVariableId] future) {
	Type[TypeVariableId] result;
	foreach (variable, type; future) {
		if (!(variable in temporaries)) {
			result[variable] = type;
		}
	}
	return result;
}

void assertCombineProperties(Type[TypeVariableId] current, Type[TypeVariableId] future) {
	auto currentDomain = current.byKey;
	auto futureRange = future.substitutionRange;
	foreach (variable; currentDomain) {
		assert(!(variable in futureRange));
	}
}

Type[TypeVariableId] combineSubstitutions(Type[TypeVariableId] current0, Type[TypeVariableId] future0) {
	assertCombineProperties(current0, future0);
	auto temporaries = current0.substitutionRange;
	auto current1 = current0.specialize(future0);
	auto future1 = removeTemporaries(temporaries, future0);
	return mergeMapsUnique(current1, future1);
}

Type[TypeVariableId] continueSubsitution(T)(Type[TypeVariableId] current, T equation) {
	auto future = typeMatch(equation.specialize(current));
	auto result = combineSubstitutions(current, future);
	return result;
}

void assertProperties(TypeVariable[TypeVariableId] input, Type[TypeVariableId] solution) {
	foreach (variable; input.byKey) {
		auto range = solution.substitutionRange;
		assert(!(variable in range), variable.to!string ~ " found in " ~ range.to!string);
	}
	foreach (variable; input.byKey) {
		assert(variable in solution);
	}
	foreach (variable, type; solution) {
		assert(variable in input);
	}
}

// no type variables from any of the equations should appear in range of result
// all type variables from all of the equations must appear in the domain of the result
Type[TypeVariableId] typeMatch(Equivalence[] equations) {
	if (equations.empty) {
		return null;
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

Type[TypeVariableId] typeMatch(Equivalence equation) {
	return typeMatch(equation.left, equation.right, equation.position);
}

Type[TypeVariableId] typeMatch(Type left, Type right, Position position) {
	return left.typeMatch(right, position);
}

bool checkRigidity(TypeVariable left, TypeVariable right) {
	auto leftRigidity = left.rigidity.mapValues!(a => tuple());
	auto rightRigidity = right.rigidity.mapValues!(a => tuple());
	auto leftConstraints = left.constraints.mapValues!(a => tuple());
	auto rightConstraints = right.constraints.mapValues!(a => tuple());
	auto common = intersectSets(leftRigidity, rightRigidity);
	auto valid = common.byKey.map!(context => left.rigidity[context] is right.rigidity[context]).all;
	if (left.rigidity.length != 0) {
		valid &= isSubSet(rightConstraints, leftConstraints);
	}
	if (right.rigidity.length != 0) {
		valid &= isSubSet(leftConstraints, rightConstraints);
	}
	return valid;
}

Type[TypeVariableId] typeMatchImpl(T1, T2)(T1 left, T2 right, Position position) {
	auto result = typeMatchImplReal(left, right, position);
	version (assert) {
		auto input = freeVariables(left, right);
		assertProperties(input, result);
	}
	return result;
}

//the heart of the compiler

// no type variables from left or right, should appear in the range of the result
// all type variables from left or right should in domain of result
Type[TypeVariableId] typeMatchImplReal(T1, T2)(T1 left, T2 right, Position position) {
	static if (is(T1 : TypeVariable) && is(T2 : TypeVariable)) {
		if (checkRigidity(left, right)) {
			auto fresh = freshSubstitution(left.constraints, right.constraints);
			auto clashing = intersectMaps(left.constraints, right.constraints);
			auto pending = clashing.byValue.map!(a => a[0].predicateMatch(a[1], position)).joiner.array;
			auto result = continueSubsitution(fresh, pending);
			auto total = mergeMapsLeft(left.constraints, right.constraints).specialize(result);

			auto rigid = mergeMapsLeft(left.rigidity, right.rigidity);
			auto joined = make!TypeVariable(make!TypeVariableId(""), total, rigid);
			return mergeMapsLeft([left.id: joined.convert!Type, right.id: joined.convert!Type], result);
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
		return null;
	} else static if (is(T1 : TypeChar) && is(T2 : TypeChar)) {
		return null;
	} else static if (is(T1 : TypeInt) && is(T2 : TypeInt)) {
		if (left.size == right.size && left.signed == right.signed) {
			return null;
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
	}
	error("Can't match " ~ left.toString ~ " to " ~ right.toString, position);
	assert(0);
}

void occuranceCheck(TypeVariable qualified, Type type, Position position) {
	if (qualified.id in type.freeVariables) {
		error("Recursive use of variable " ~ qualified.to!string ~ " in " ~ type.to!string, position);
	}
}

Type[TypeVariableId] qualifiedInstantiate(TypeVariable qualified, Type type, Position position) {
	auto fresh = freshSubstitution(type, qualified.constraints);
	auto pending = qualified.constraints.byValue.map!(a => predicateInstantiate(a, type, position)).joiner.array;
	auto result = continueSubsitution(fresh, pending);
	result[qualified.id] = type.specialize(result);
	version (assert) {
		auto input = freeVariables(qualified, type);
		assertProperties(input, result);
	}
	return result;
}

Equivalence[] predicateInstantiate(Predicate predicate, Type type, Position position) {
	return predicate.predicateInstantiate(type, position);
}

Equivalence[] predicateInstantiateImpl(C, T)(C constraint, T type, Position position) {
	static if (is(C : PredicateNumber) && is(T : TypeInt)) {
		return [];
	} else static if (is(C : PredicateTuple) && is(T : TypeStruct)) {
		if (constraint.index < type.values.length) {
			return [Equivalence(constraint.type, type.values[constraint.index], position)];
		}
	}
	error("Can't match constraint " ~ constraint.toString ~ " to " ~ type.toString, position);
	assert(0);
}

Equivalence[] predicateMatchImpl(C)(C left, C right, Position position) {
	static if (is(C : PredicateNumber)) {
		return [];
	} else static if (is(C : PredicateTuple)) {
		assert(left.index == right.index);
		return [Equivalence(left.type, right.type, position)];
	} else {
		static assert(0);
	}
}

TypeVariable[TypeVariableId] freeVariables(T)(T item) if (is(T : Type) || is(T : Predicate)) {
	return item.freeVariables;
}

TypeVariable[TypeVariableId] freeVariables(R)(R data) if (isInputRange!R) {
	return data.map!(a => a.freeVariables)
		.fold!mergeMapsLeft(emptyMap!(TypeVariableId, TypeVariable));
}

TypeVariable[TypeVariableId] freeVariables(T...)(T arguments) if (T.length > 1) {
	return mergeMapsLeft(arguments[0 .. $ - 1].freeVariables, arguments[$ - 1].freeVariables);
}

TypeVariable[TypeVariableId] freeVariables(K, V)(V[K] data) {
	return data.byValue.freeVariables;
}

auto specialize(T)(T[] data, Type[TypeVariableId] moves) {
	return data.map!(a => a.specialize(moves)).array;
}

auto specialize(K, V)(V[K] data, Type[TypeVariableId] moves) {
	return data.mapValues!(a => a.specialize(moves));
}

auto specialize(T)(Lazy!T data, Type[TypeVariableId] moves) {
	return defer(() => data.get.specialize(moves));
}

auto toRuntime(T)(T[] data) {
	return data.map!(a => a.toRuntime()).array;
}

auto toRuntime(T)(Lazy!T data) {
	return defer(() => data.get.toRuntime);
}
