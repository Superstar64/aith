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

mixin template DefaultMorph(T) {
	T specialize(Type[PolymorphicVariable] moves) {
		return visit1!(make!T, a => a.specialize(moves))(this);
	}

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

TypeMetaclass metaclass;
static this() {
	metaclass = new TypeMetaclass();
	metaclass._type = metaclass;
}

class Impl(T : Type) : T {
	mixin Getters!T;

	CompileTimeType type() {
		return metaclass;
	}

	Tuple!()[PolymorphicVariable] generics() {
		return genericsImpl(this);
	}

	mixin DefaultMorph!T;
	mixin DefaultCast;

	override string toString() {
		return toStringImpl(this);
	}
}

class Impl(T : PolymorphicVariable) : T {
	CompileTimeType type() {
		return metaclass;
	}

	override Tuple!()[PolymorphicVariable] generics() {
		return [this: tuple()];
	}

	override Type specialize(Type[PolymorphicVariable] moves) {
		if (this in moves) {
			return moves[this];
		} else {
			return this;
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

class Impl(T : TuplePolymorphicVariable) : TuplePolymorphicVariable {
	mixin Getters!T;

	CompileTimeType type() {
		return metaclass;
	}

	Tuple!()[PolymorphicVariable] generics() {
		return genericsImpl(this);
	}

	override Type specialize(Type[PolymorphicVariable] moves) {
		if (id in moves) {
			return moves[id];
		} else {
			return new Impl!TuplePolymorphicVariable(id,
					values.map!(a => a.specialize(moves)).array);
		}
	}

	mixin DefaultCast;

	override Codegen.Type toRuntime() {
		assert(0);
	}
}

// visit with generics

auto visit1(alias construct, alias f, T : ModuleVar)(T that) {
	with (that)
		return construct(f(type), f(generics), f(value), name, strong, id);
}

auto visit1(alias construct, alias f, T : NamedPattern)(T that) {
	with (that)
		return construct(f(type), f(argument));
}

auto visit1(alias construct, alias f, T : TuplePattern)(T that) {
	with (that)
		return construct(f(type), f(matches));
}

auto visit1(alias construct, alias f, T : FunctionLiteral)(T that) {
	with (that)
		return construct(f(type), f(generics), name, strong, id, f(argument), f(text));
}

auto visit1(alias construct, alias f, T : FunctionArgument)(T that) {
	with (that)
		return construct(f(type), f(generics), name, id);
}

auto visit1(alias construct, alias f, T : ScopeVar)(T that) {
	with (that)
		return construct(f(type), f(generics), name, id);
}

auto visit1(alias construct, alias f, T : ScopeVarDef)(T that) {
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
		return construct(f(type), f(generics), f(value));
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

// visit without generics

auto visit2(alias construct, alias f, T : ModuleVar)(T that) {
	with (that)
		return construct(f(type), f(value), name, strong, id);
}

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

auto visit2(alias construct, alias f, T : FunctionArgument)(T that) {
	with (that)
		return construct(f(type), name, id);
}

auto visit2(alias construct, alias f, T : ScopeVar)(T that) {
	with (that)
		return construct(f(type), name, id);
}

auto visit2(alias construct, alias f, T : ScopeVarDef)(T that) {
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
		return construct(f(type), f(value));
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

Tuple!()[PolymorphicVariable] genericsImpl(TuplePolymorphicVariable that) {
	return arrayToSet(that.values.map!(a => a.generics.byKey).joiner.array ~ that.id);
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

string toStringImpl(NormalPolymorphicVariable that) {
	return (cast(void*) that).to!string;
}

string toStringImpl(NumberPolymorphicVariable that) {
	return (cast(void*) that).to!string ~ " extends number";
}

string toStringImpl(TuplePolymorphicVariableImpl that) {
	return (cast(void*) that).to!string ~ " extends tuple";
}

string toStringImpl(TuplePolymorphicVariable that) {
	return that.id.toString ~ "(" ~ that.values.to!string ~ ")";
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

class Impl(T : TypeImport) : T {
	mixin Getters!T;
	CompileTimeType type() {
		return metaclass;
	}

	mixin DefaultCast;

	override string toString() {
		return "import";
	}
}

struct Subsitution {
	PolymorphicVariable from;
	Type to;

	string toString() {
		return .to!string(from) ~ " = " ~ .to!string(to);
	}
}

alias PolyTypes = AliasSeq!(TypeBool, TypeChar, TypeInt, TypeStruct,
		TypePointer, TypeArray, TypeArray, TypeFunction, TypeFunction,
		NumberPolymorphicVariable, TuplePolymorphicVariable, NormalPolymorphicVariable);
//todo use virtual table dispatch for this
Subsitution[] typeMatch(Type a, Type b, Position position) {
	return dispatch!((a, b) => dispatch!((a, b) => typeMatchImpl(b, a, position), PolyTypes)(b, a),
			PolyTypes)(a, b);
}

Subsitution[] typeMatchImpl(T1, T2)(T1 left, T2 right, Position position) {
	if ((cast(Object) left) is(cast(Object) right)) {
		return [];
	}
	static if (is(T1 == NormalPolymorphicVariable)) {
		return [Subsitution(left, right)];
	} else static if (is(T2 == NormalPolymorphicVariable)) {
		return [Subsitution(right, left)];
	} else static if (is(T1 == NumberPolymorphicVariable) && is(T2 == NumberPolymorphicVariable)) {
		return [Subsitution(left, right)];
	} else static if (is(T1 == NumberPolymorphicVariable) && is(T2 == TypeInt)) {
		return [Subsitution(left, right)];
	} else static if (is(T1 == TypeInt) && is(T2 == NumberPolymorphicVariable)) {
		return [Subsitution(right, left)];
	} else static if (is(T1 == TuplePolymorphicVariable) && is(T2 == TuplePolymorphicVariable)) {
		auto common = zip(left.values, right.values).map!(a => typeMatch(a.expand,
				position)).joiner.array;
		if (left.values.length < right.values.length) {
			common ~= Subsitution(left.id, right.id);
		} else {
			common ~= Subsitution(right.id, left.id);
		}
		return common;
	} else static if (is(T1 == TuplePolymorphicVariable) && is(T2 == TypeStruct)) {
		if (left.values.length <= right.values.length) {
			return zip(left.values, right.values).map!(a => typeMatch(a.expand,
					position)).joiner.array ~ Subsitution(left.id, right);
		}
	} else static if (is(T1 == TypeStruct) && is(T2 == TuplePolymorphicVariable)) {
		if (left.values.length >= right.values.length) {
			return zip(left.values, right.values).map!(a => typeMatch(a.expand,
					position)).joiner.array ~ Subsitution(right.id, left);
		}
	} else static if (is(T1 == TypeBool) && is(T2 == TypeBool)) {
		return [];
	} else static if (is(T1 == TypeChar) && is(T2 == TypeChar)) {
		return [];
	} else static if (is(T1 == TypeInt) && is(T2 == TypeInt)) {
		if (left.size == right.size) {
			return [];
		}
	} else static if (is(T1 == TypeStruct) && is(T2 == TypeStruct)) {
		if (left.values.length == right.values.length) {
			return zip(left.values, right.values).map!(a => typeMatch(a.expand,
					position)).joiner.array;
		}
	} else static if (is(T1 == TypeArray) && is(T2 == TypeArray)) {
		return typeMatch(left.array, right.array, position);
	} else static if (is(T1 == TypeFunction) && is(T2 == TypeFunction)) {
		return typeMatch(left.result, right.result, position) ~ typeMatch(left.argument,
				right.argument, position);
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

Tuple!()[PolymorphicVariable] specialize(Tuple!()[PolymorphicVariable] generics,
		Type[PolymorphicVariable] moves) {
	return generics.keys.map!(a => a.specialize(moves).generics.keys).joiner.array.arrayToSet;
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
