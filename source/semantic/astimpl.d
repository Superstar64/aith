module semantic.astimpl;

import std.meta;
import std.typecons;
import std.conv;
import std.algorithm;
import std.range;
import misc;

import genericast;

public import semantic.ast;
static import Codegen = codegen.astimpl;
static import Parser = parser.ast;

template make(T) {
	T make(A...)(A args) {
		return new Impl!T(args);
	}
}

template make(T : Scheme) {
	T make(PolymorphicVariable variable) {
		return new Impl!T(variable, emptyArray!Constraint);
	}

	T make(PolymorphicVariable variable, Constraint[] constraints) {
		return new Impl!T(variable, constraints);
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
	T specialize(Type[PolymorphicVariable] moves) {
		return visit1!(make!T, a => a.specialize(moves))(this);
	}
}

mixin template DefaultMorph(T) {
	mixin DefaultSpecialize!T;

	RuntimeType!T toRuntime() {
		return visit2!(Codegen.make!(RuntimeType!T), a => a.toRuntime())(this);
	}
}

class Impl(T) : T {
	mixin Getters!T;
	mixin DefaultCast;
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

	Tuple!()[PolymorphicVariable] generics() {
		return genericsImpl(this);
	}

	mixin DefaultMorph!T;
	mixin DefaultCast;

	override string toString() {
		return toStringImpl(this);
	}
}

class Impl(T : Constraint) : T {
	mixin Getters!T;

	Tuple!()[PolymorphicVariable] generics() {
		return genericsImpl(this);
	}

	mixin DefaultSpecialize!T;
	mixin DefaultCast;

	override string toString() {
		return toStringImpl(this);
	}
}

class Impl(T : Scheme) : T {
	mixin Getters!T;
	override Tuple!()[PolymorphicVariable] generics() {
		auto extra = constraints.map!(a => a.generics)
			.fold!mergeSets(emptySet!PolymorphicVariable);
		return mergeSets(extra, [variable: tuple()]);
	}

	override Type specialize(Type[PolymorphicVariable] moves) {
		if (variable in moves) {
			return moves[variable];
		} else {
			return make!Scheme(variable, constraints.map!(a => a.specialize(moves)).array);
		}
	}

	Codegen.Type toRuntime() {
		assert(0);
	}

	mixin DefaultCast;

	override string toString() {
		return toStringImpl(this);
	}
}

// visit with generics

auto visit1(alias construct, alias f, T : NamedPattern)(T that) {
	with (that)
		return construct(f(type), f(generics), f(argument));
}

auto visit1(alias construct, alias f, T : TuplePattern)(T that) {
	with (that)
		return construct(f(type), f(generics), f(matches));
}

auto visit1(alias construct, alias f, T : FunctionLiteral)(T that) {
	with (that)
		return construct(f(type), f(generics), name, strong, id, f(argument), f(text));
}

auto visit1(alias construct, alias f, T : Variable)(T that) {
	with (that)
		return construct(f(type), f(generics), name, id);
}

auto visit1(alias construct, alias f, T : VariableDef)(T that) {
	with (that)
		return construct(f(type), f(generics), f(variable), f(value), f(last));
}

auto visit1(alias construct, alias f, T : IntLit)(T that) {
	with (that)
		return construct(f(type), f(generics), value);
}

auto visit1(alias construct, alias f, T : CharLit)(T that) {
	with (that)
		return construct(f(type), f(generics), value);
}

auto visit1(alias construct, alias f, T : BoolLit)(T that) {
	with (that)
		return construct(f(type), f(generics), yes);
}

auto visit1(alias construct, alias f, T : TupleLit)(T that) {
	with (that)
		return construct(f(type), f(generics), f(values));
}

auto visit1(alias construct, alias f, T : If)(T that) {
	with (that)
		return construct(f(type), f(generics), f(cond), f(yes), f(no));
}

auto visit1(alias construct, alias f, T : While)(T that) {
	with (that)
		return construct(f(type), f(generics), f(cond), f(state));
}

auto visit1(alias construct, alias f, T : New)(T that) {
	with (that)
		return construct(f(type), f(generics), f(value));
}

auto visit1(alias construct, alias f, T : NewArray)(T that) {
	with (that)
		return construct(f(type), f(generics), f(length), f(value));
}

auto visit1(alias construct, alias f, T : CastInteger)(T that) {
	with (that)
		return construct(f(type), f(generics), f(value));
}

auto visit1(alias construct, alias f, T : Length)(T that) {
	with (that)
		return construct(f(type), f(generics));
}

auto visit1(alias construct, alias f, T : Index)(T that) {
	with (that)
		return construct(f(type), f(generics), f(array), f(index));
}

auto visit1(alias construct, alias f, T : IndexAddress)(T that) {
	with (that)
		return construct(f(type), f(generics), f(array), f(index));
}

auto visit1(alias construct, alias f, T : TupleIndex)(T that) {
	with (that)
		return construct(f(type), f(generics), f(tuple), index);
}

auto visit1(alias construct, alias f, T : TupleIndexAddress)(T that) {
	with (that)
		return construct(f(type), f(generics), f(tuple), index);
}

auto visit1(alias construct, alias f, T : Call)(T that) {
	with (that)
		return construct(f(type), f(generics), f(calle), f(argument));
}

auto visit1(alias construct, alias f, T : Slice)(T that) {
	with (that)
		return construct(f(type), f(generics), f(array), f(left), f(right));
}

auto visit1(alias construct, alias f, T : Binary!op, string op)(T that) {
	with (that)
		return construct(f(type), f(generics), f(left), f(right));
}

auto visit1(alias construct, alias f, T : Prefix!op, string op)(T that) {
	with (that)
		return construct(f(type), f(generics), f(value));
}

auto visit1(alias construct, alias f, T : Deref)(T that) {
	with (that)
		return construct(f(type), f(generics), f(value));
}

auto visit1(alias construct, alias f, T : Scope)(T that) {
	with (that)
		return construct(f(type), f(generics), f(pass), f(last));
}

auto visit1(alias construct, alias f, T : Assign)(T that) {
	with (that)
		return construct(f(type), f(generics), f(left), f(right), f(last));
}

auto visit1(alias construct, alias f, T : StringLit)(T that) {
	with (that)
		return construct(f(type), f(generics), value);
}

auto visit1(alias construct, alias f, T : ArrayLit)(T that) {
	with (that)
		return construct(f(type), f(generics), f(values));
}

auto visit1(alias construct, alias f, T : ExternJs)(T that) {
	with (that)
		return construct(f(type), f(generics), name);
}

auto visit1(alias construct, alias f, T : TypeBool)(T that) {
	with (that)
		return construct();
}

auto visit1(alias construct, alias f, T : TypeChar)(T that) {
	with (that)
		return construct();
}

auto visit1(alias construct, alias f, T : TypeInt)(T that) {
	with (that)
		return construct(size, signed);
}

auto visit1(alias construct, alias f, T : TypeStruct)(T that) {
	with (that)
		return construct(f(values));
}

auto visit1(alias construct, alias f, T : TypeArray)(T that) {
	with (that)
		return construct(f(array));
}

auto visit1(alias construct, alias f, T : TypeFunction)(T that) {
	with (that)
		return construct(f(result), f(argument));
}

auto visit1(alias construct, alias f, T : TypePointer)(T that) {
	with (that)
		return construct(f(value));
}

auto visit1(alias construct, alias f, T : ConstraintNumber)(T that) {
	with (that)
		return construct();
}

auto visit1(alias construct, alias f, T : ConstraintTuple)(T that) {
	with (that)
		return construct(index, f(type));
}

// visit without generics

auto visit2(alias construct, alias f, T : NamedPattern)(T that) {
	with (that)
		return construct(f(type), f(argument));
}

auto visit2(alias construct, alias f, T : TuplePattern)(T that) {
	with (that)
		return construct(f(type), f(matches));
}

auto visit2(alias construct, alias f, T : FunctionLiteral)(T that) {
	with (that)
		return construct(f(type), name, strong, id, f(argument), f(text));
}

auto visit2(alias construct, alias f, T : Variable)(T that) {
	with (that)
		return construct(f(type), name, id);
}

auto visit2(alias construct, alias f, T : VariableDef)(T that) {
	with (that)
		return construct(f(type), f(variable), f(value), f(last));
}

auto visit2(alias construct, alias f, T : IntLit)(T that) {
	with (that)
		return construct(f(type), value);
}

auto visit2(alias construct, alias f, T : CharLit)(T that) {
	with (that)
		return construct(f(type), value);
}

auto visit2(alias construct, alias f, T : BoolLit)(T that) {
	with (that)
		return construct(f(type), yes);
}

auto visit2(alias construct, alias f, T : TupleLit)(T that) {
	with (that)
		return construct(f(type), f(values));
}

auto visit2(alias construct, alias f, T : If)(T that) {
	with (that)
		return construct(f(type), f(cond), f(yes), f(no));
}

auto visit2(alias construct, alias f, T : While)(T that) {
	with (that)
		return construct(f(type), f(cond), f(state));
}

auto visit2(alias construct, alias f, T : New)(T that) {
	with (that)
		return construct(f(type), f(value));
}

auto visit2(alias construct, alias f, T : NewArray)(T that) {
	with (that)
		return construct(f(type), f(length), f(value));
}

auto visit2(alias construct, alias f, T : CastInteger)(T that) {
	with (that)
		return construct(f(type), f(value));
}

auto visit2(alias construct, alias f, T : Length)(T that) {
	with (that)
		return construct(f(type));
}

auto visit2(alias construct, alias f, T : Index)(T that) {
	with (that)
		return construct(f(type), f(array), f(index));
}

auto visit2(alias construct, alias f, T : IndexAddress)(T that) {
	with (that)
		return construct(f(type), f(array), f(index));
}

auto visit2(alias construct, alias f, T : TupleIndex)(T that) {
	with (that)
		return construct(f(type), f(tuple), index);
}

auto visit2(alias construct, alias f, T : TupleIndexAddress)(T that) {
	with (that)
		return construct(f(type), f(tuple), index);
}

auto visit2(alias construct, alias f, T : Call)(T that) {
	with (that)
		return construct(f(type), f(calle), f(argument));
}

auto visit2(alias construct, alias f, T : Slice)(T that) {
	with (that)
		return construct(f(type), f(array), f(left), f(right));
}

auto visit2(alias construct, alias f, T : Binary!op, string op)(T that) {
	with (that)
		return construct(f(type), f(left), f(right));
}

auto visit2(alias construct, alias f, T : Prefix!op, string op)(T that) {
	with (that)
		return construct(f(type), f(value));
}

auto visit2(alias construct, alias f, T : Deref)(T that) {
	with (that)
		return construct(f(type), f(value));
}

auto visit2(alias construct, alias f, T : Scope)(T that) {
	with (that)
		return construct(f(type), f(pass), f(last));
}

auto visit2(alias construct, alias f, T : Assign)(T that) {
	with (that)
		return construct(f(type), f(left), f(right), f(last));
}

auto visit2(alias construct, alias f, T : StringLit)(T that) {
	with (that)
		return construct(f(type), value);
}

auto visit2(alias construct, alias f, T : ArrayLit)(T that) {
	with (that)
		return construct(f(type), f(values));
}

auto visit2(alias construct, alias f, T : ExternJs)(T that) {
	with (that)
		return construct(f(type), name);
}

auto visit2(alias construct, alias f, T : TypeBool)(T that) {
	with (that)
		return construct();
}

auto visit2(alias construct, alias f, T : TypeChar)(T that) {
	with (that)
		return construct();
}

auto visit2(alias construct, alias f, T : TypeInt)(T that) {
	with (that)
		return construct(size, signed);
}

auto visit2(alias construct, alias f, T : TypeStruct)(T that) {
	with (that)
		return construct(f(values));
}

auto visit2(alias construct, alias f, T : TypeArray)(T that) {
	with (that)
		return construct(f(array));
}

auto visit2(alias construct, alias f, T : TypeFunction)(T that) {
	with (that)
		return construct(f(result), f(argument));
}

auto visit2(alias construct, alias f, T : TypePointer)(T that) {
	with (that)
		return construct(f(value));
}

Tuple!()[PolymorphicVariable] genericsImpl(TypeBool that) {
	return null;
}

Tuple!()[PolymorphicVariable] genericsImpl(TypeChar that) {
	return null;
}

Tuple!()[PolymorphicVariable] genericsImpl(TypeInt that) {
	return null;
}

Tuple!()[PolymorphicVariable] genericsImpl(TypeStruct that) {
	return that.values.map!(a => a.generics.keys).joiner.array.arrayToSet;
}

Tuple!()[PolymorphicVariable] genericsImpl(TypeArray that) {
	return that.array.generics;
}

Tuple!()[PolymorphicVariable] genericsImpl(TypeFunction that) {
	return mergeSets(that.result.generics, that.argument.generics);
}

Tuple!()[PolymorphicVariable] genericsImpl(TypePointer that) {
	return that.value.generics;
}

Tuple!()[PolymorphicVariable] genericsImpl(ConstraintNumber that) {
	return null;
}

Tuple!()[PolymorphicVariable] genericsImpl(ConstraintTuple that) {
	return that.type.generics;
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

string toString(PolymorphicVariable that) {
	return (cast(void*) that).to!string;
}

string toStringImpl(Scheme that) {
	string result;
	result ~= that.to!string();
	result ~= " extends (";
	result ~= that.constraints.map!(a => a.to!string()).joiner(",").array.to!string;
	result ~= ")";
	return result;
}

string toStringImpl(ConstraintNumber that) {
	return "number";
}

string toStringImpl(ConstraintTuple that) {
	return that.index.to!string ~ " : " ~ that.type.to!string;
}

alias RuntimeTypes = AliasSeq!(TypeBool, TypeChar, TypeInt, TypeStruct, TypePointer, TypeArray, TypeArray, TypeFunction, TypeFunction);

//todo use virtual table dispatch for this
Type[PolymorphicVariable] typeMatch(Type a, Type b, Position position) {
	alias PolyTypes = AliasSeq!(RuntimeTypes, Scheme);
	return dispatch!((a, b) => dispatch!((a, b) => typeMatchImpl(b, a, position), PolyTypes)(b, a), PolyTypes)(a, b);
}

alias Constraints = AliasSeq!(ConstraintNumber, ConstraintTuple);

Type[PolymorphicVariable] constraintMatch(Constraint constraint, Type type, Position position) {
	return dispatch!((a, b) => dispatch!((b, a) => constraintMatchImpl(a, b, position), RuntimeTypes)(b, a), Constraints)(constraint, type);
}

Type[PolymorphicVariable] constraintMatchImpl(C, T)(C constraint, T type, Position position) {
	static if (is(C == ConstraintNumber) && is(T == TypeInt)) {
		return null;
	} else static if (is(C == ConstraintTuple) && is(T == TypeStruct)) {
		if (constraint.index < type.values.length) {
			return typeMatch(constraint.type, type.values[constraint.index], position);
		}
	}
	error("Can't match constraint " ~ constraint.toString ~ " to " ~ type.toString, position);
	assert(0);
}

Type[PolymorphicVariable] typeMatchImpl(T1, T2)(T1 left, T2 right, Position position) {
	if ((cast(Object) left) is(cast(Object) right)) {
		return null;
	}
	static if (is(T1 == Scheme) && is(T2 == Scheme)) {
		auto joined = make!Scheme(make!PolymorphicVariable, left.constraints ~ right.constraints);
		return [left.variable: joined, right.variable: joined];
	} else static if (is(T1 == Scheme) && !is(T2 == Scheme)) {
		auto extra = left.constraints
			.map!(a => constraintMatch(a, right, position))
			.fold!mergeMaps(emptyMap!(PolymorphicVariable, Type));
		return mergeMaps(extra, [left.variable: right]);
	} else static if (!is(T1 == Scheme) && is(T2 == Scheme)) {
		auto extra = right.constraints
			.map!(a => constraintMatch(a, left, position))
			.fold!mergeMaps(emptyMap!(PolymorphicVariable, Type));
		return mergeMaps(extra, [right.variable: left]);
	} else static if (is(T1 == TypeBool) && is(T2 == TypeBool)) {
		return null;
	} else static if (is(T1 == TypeChar) && is(T2 == TypeChar)) {
		return null;
	} else static if (is(T1 == TypeInt) && is(T2 == TypeInt)) {
		if (left.size == right.size) {
			return null;
		}
	} else static if (is(T1 == TypeStruct) && is(T2 == TypeStruct)) {
		if (left.values.length == right.values.length) {
			return zip(left.values, right.values).map!(a => typeMatch(a.expand, position))
				.fold!mergeMaps(emptyMap!(PolymorphicVariable, Type));
		}
	} else static if (is(T1 == TypeArray) && is(T2 == TypeArray)) {
		return typeMatch(left.array, right.array, position);
	} else static if (is(T1 == TypeFunction) && is(T2 == TypeFunction)) {
		return mergeMaps(typeMatch(left.result, right.result, position), typeMatch(left.argument, right.argument, position));
	} else static if (is(T1 == TypePointer) && is(T2 == TypePointer)) {
		return typeMatch(left.value, right.value, position);
	}
	error("Can't match " ~ left.toString ~ " to " ~ right.toString, position);
	assert(0);
}

mixin template TypeImpl() {
	CompileTimeType type() {
		return metaclass;
	}
}

Tuple!()[PolymorphicVariable] specialize(Tuple!()[PolymorphicVariable] generics, Type[PolymorphicVariable] moves) {
	return generics.keys
		.map!(a => make!Scheme(a))
		.map!(a => a.specialize(moves).generics.keys)
		.joiner
		.array
		.arrayToSet;
}

auto specialize(T)(T[] data, Type[PolymorphicVariable] moves) {
	return data.map!(a => a.specialize(moves)).array;
}

auto specialize(T)(Lazy!T data, Type[PolymorphicVariable] moves) {
	return defer(() => data.get.specialize(moves));
}

auto toRuntime(T)(T[] data) {
	return data.map!(a => a.toRuntime()).array;
}

auto toRuntime(T)(Lazy!T data) {
	return defer(() => data.get.toRuntime);
}
