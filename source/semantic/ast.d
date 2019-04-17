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

import std.algorithm;
import std.array;
import std.bigint;
import std.range;
import std.meta;
import std.typecons;
import std.conv;
import std.traits;

import jsast;

static import Parser = parser.ast;
import misc;

//vtables need theses
import semantic.semantic : Context;
import codegen : Usage, Extra, Case, generateJsImpl, generateJsIntoVarImpl,
	generateJsAddressOfImpl, generateJsEffectsOnlyImpl, generateSymbolImpl;

enum TupleLitKind {
	normal,
	poly,
	compile
}

struct Wrapper(T) {
	T _value;
	Position position;

	alias _value this;

	this(T _value, Position position) {
		this._value = _value;
		this.position = position;
	}
}

template mapWrap(alias fun) {
	auto mapWrap(Element)(Wrapper!Element wrapper) {
		return Wrapper!(typeof(fun(wrapper._value)))(fun(wrapper._value), wrapper.position);
	}
}

auto wrapper(T)(T value, Position position) {
	return Wrapper!T(value, position);
}

class Transition {
	Expression[Expression] replacements;
	Module source;
	Tuple!()[PolymorphicVariable] functionVariables;
	this(Module source) {
		this.source = source;
	}
}

interface Expression {
	CompileTimeType typeVirtual();
	final type() {
		return typeVirtual;
	}
}

interface PolymorphicExpression : Expression {
	PolymorphicType typeVirtual();
	final type() {
		return typeVirtual;
	}

	PolymorphicExpression specialize(PolymorphicType[PolymorphicVariable] moves,
			Transition transition);
}

interface RuntimeExpression : PolymorphicExpression {
	Type typeVirtual();
	final type() {
		return typeVirtual;
	}

	JsExpr generateJs(Usage usage, JsScope depend, Extra* extra);
	void generateJsIntoVar(JsLit variable, bool createVar, Case shouldCopy,
			JsScope depend, Extra* extra);
	//todo print warning if unusal node(new,intlit,etc)
	void generateJsEffectsOnly(JsScope depend, Extra* extra);
}

interface PolymorphicLValueExpression : PolymorphicExpression {
	PolymorphicLValueExpression specialize(PolymorphicType[PolymorphicVariable] moves,
			Transition transition);
}

interface LValueExpression : PolymorphicLValueExpression, RuntimeExpression {
	Type typeVirtual();
	final type() {
		return typeVirtual;
	}

	JsExpr generateJsAddressOf(Usage, JsScope, Extra*);
}

mixin template overrideExpression(RealType = CompileTimeType) {
	RealType type;
	override RealType typeVirtual() {
		return type;
	}
}

mixin template overridePolymorphic(RealType = PolymorphicType) {
	mixin overrideExpression!RealType;
}

mixin template overrideRuntime() {
	mixin overridePolymorphic!Type;
override:

	PolymorphicExpression specialize(PolymorphicType[PolymorphicVariable] moves,
			Transition transition) {
		return this;
	}

	JsExpr generateJs(Usage usage, JsScope depend, Extra* extra) {
		return generateJsImpl(this, usage, depend, extra);
	}

	void generateJsIntoVar(JsLit variable, bool createVar, Case shouldCopy,
			JsScope depend, Extra* extra) {
		return generateJsIntoVarImpl(this, variable, createVar, shouldCopy, depend, extra);
	}

	void generateJsEffectsOnly(JsScope depend, Extra* extra) {
		return generateJsEffectsOnlyImpl(this, depend, extra);
	}
}

mixin template overrideLValue() {
	mixin overrideRuntime;

override:
	PolymorphicLValueExpression specialize(PolymorphicType[PolymorphicVariable] moves,
			Transition transition) {
		return this;
	}

	JsExpr generateJsAddressOf(Usage usage, JsScope depend, Extra* extra) {
		return generateJsAddressOfImpl(this, usage, depend, extra);
	}
}

alias PickExpression(TupleLitKind kind : TupleLitKind.normal) = RuntimeExpression;
alias PickExpression(TupleLitKind kind : TupleLitKind.poly) = PolymorphicExpression;
alias PickExpression(TupleLitKind kind : TupleLitKind.compile) = Expression;
alias PickExpression(bool runtime : true) = RuntimeExpression;
alias PickExpression(bool runtime : false) = PolymorphicExpression;

alias PickExpressionLValue(bool runtime : true) = LValueExpression;
alias PickExpressionLValue(bool runtime : false) = PolymorphicLValueExpression;

alias MaybeLValueRuntime(bool lvalue : true) = LValueExpression;
alias MaybeLValueRuntime(bool lvalue : false) = RuntimeExpression;

alias MaybeLValuePolymorphic(bool lvalue : true) = PolymorphicLValueExpression;
alias MaybeLValuePolymorphic(bool lvalue : false) = PolymorphicExpression;

alias overrideGenericImpl(TupleLitKind kind : TupleLitKind.normal) = overrideRuntime;
alias overrideGenericImpl(TupleLitKind kind : TupleLitKind.poly) = overridePolymorphic;
alias overrideGenericImpl(TupleLitKind kind : TupleLitKind.compile) = overrideExpression;
alias overrideGenericImpl(bool runtime : true) = overrideRuntime;
alias overrideGenericImpl(bool runtime : false) = overridePolymorphic;

alias overrideGenericLValueImpl(bool runtime : true) = overrideLValue;
alias overrideGenericLValueImpl(bool runtime : false) = overridePolymorphic;

//avoids wierd compiler error
//todo remove lator
mixin template overrideGeneric(bool kind) {
	alias target_ = overrideGenericImpl!kind;
	mixin target_;
}

mixin template overrideGeneric(TupleLitKind kind) {
	alias target_ = overrideGenericImpl!kind;
	mixin target_;
}

mixin template overrideGenericLValue(bool kind) {
	alias target_ = overrideGenericLValueImpl!kind;
	mixin target_;
}

auto specializeMap(Tuple)(Tuple tuple) {
	return tuple[0].mapWrap!(a => a.specialize(tuple[1], tuple[2]));
}

auto specializeRegular(Tuple)(Tuple tuple) {
	return tuple[0].specialize(tuple[1], tuple[2]);
}

auto specializeMapList(Tuple)(Tuple tuple) {
	return tuple[0].map!(a => a.mapWrap!(b => b.specialize(tuple[1], tuple[2]))).array;
}

auto specializeIgnore(Tuple)(Tuple tuple) {
	return tuple[0];
}

mixin template overrideSpecialize(bool runtime, alias create, alias symbols,
		alias maps, Return = PolymorphicExpression, alias postfix = (a, b, c) {}) {
	static if (!runtime) {
		override Return specialize(PolymorphicType[PolymorphicVariable] moves, Transition transition) {
			if (this in transition.replacements) {
				return transition.replacements[this].castTo!Return;
			}
			auto result = create(tupleCall!(maps)(tupleMap!(s => std.typecons.tuple(s,
					moves, transition))(symbols.expand).expand).expand);
			transition.replacements[this] = result;
			postfix(result, moves, transition);
			return result;
		}
	}
}

// "macro" for creating specializable expressions
template creater(alias target, alias checks, alias validMaps, Return = PolymorphicExpression) {
	Return creater(T...)(T args) {
		bool valid = true;
		foreach (c, check; checks.expand) {
			valid = valid && !!check(args[c]);
		}
		if (valid) {
			return new target!true(tupleCall!validMaps(args).expand);
		} else {
			return new target!false(args);
		}
	}
}

alias createrIgnoreMap = a => a;
alias createrIgnoreCheck = a => true;

alias createrRuntimeCheck = castTo!RuntimeExpression;
alias createrRuntimeMap = mapWrap!(castTo!RuntimeExpression);

alias createrRuntimeListCheck = a => a.map!(b => b.mapWrap!(castTo!RuntimeExpression)).all;
alias createrRuntimeListMap = a => a.map!(b => b.mapWrap!(castTo!RuntimeExpression)).array;

alias createrLValueCheck = castTo!LValueExpression;
alias createrLValueMap = mapWrap!(castTo!LValueExpression);

alias createrTypeCheck = castTo!Type;
alias createrTypeMap = castTo!Type;

class CastPartial : Expression {
	Type value;
	this(Type value) {
		this.type = new TypeCastPartial();
		this.value = value;
	}

	mixin overrideExpression;
}

class InferPartial : Expression {
	Type value;
	this(Type value) {
		this.type = new TypeInferPartial();
		this.value = value;
	}

	mixin overrideExpression;
}

class ModuleVarRef : LValueExpression {
	Wrapper!ModuleVarDef definition;
	this(Wrapper!ModuleVarDef definition) {
		this.type = definition.value.type;
		this.definition = definition;
	}

	mixin overrideLValue;
}

class Import : Expression {
	Module mod;
	this(Module mod) {
		this.type = new TypeImport();
		this.mod = mod;
	}

	mixin overrideExpression;
}

alias IntLit = IntLitImpl!true;

class IntLitImpl(bool runtime) : PickExpression!runtime {
	BigInt value;
	this(PickType!runtime type, BigInt value) {
		this.type = type;
		this.value = value;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createIntLit, Pack!(type, value),
			Pack!(specializeRegular, specializeIgnore));
}

alias createIntLit = creater!(IntLitImpl, Pack!(createrTypeCheck,
		createrIgnoreCheck), Pack!(createrTypeMap, createrIgnoreMap));

class CharLit : RuntimeExpression {
	dchar value;
	this(dchar value) {
		this.type = new TypeChar;
		this.value = value;
	}

	mixin overrideRuntime;
}

class BoolLit : RuntimeExpression {
	bool yes;
	this(bool value) {
		this.type = new TypeBool;
		this.yes = value;
	}

	mixin overrideRuntime;
}

interface TupleLitCommon : Expression {
	final Wrapper!Expression[] values() {
		return valuesVirtual();
	}

	Wrapper!Expression[] valuesVirtual();
}

alias TupleLit = TupleLitImpl!(TupleLitKind.normal);

class TupleLitImpl(TupleLitKind kind) : PickExpression!kind, TupleLitCommon {
	Wrapper!(PickExpression!kind)[] values;

	this(Wrapper!(PickExpression!kind)[] values) {

		this.type = new TypeStructImpl!kind(values.map!(a => a.type).array);
		if (values.length == 0) {
			assert(kind == TupleLitKind.normal);
		}
		this.values = values;
	}

override:
	Wrapper!Expression[] valuesVirtual() {
		return values.castToPermissive!(Wrapper!Expression[]);
	}

	mixin overrideGeneric!kind;
	mixin overrideSpecialize!(kind != TupleLitKind.poly, createTupleLitPoly,
			Pack!values, Pack!specializeMapList);
}

Expression createTupleLit(Wrapper!Expression[] values) {
	if (values.map!(a => !!a.castToPermissive!RuntimeExpression).all) {
		return new TupleLitImpl!(TupleLitKind.normal)(
				values.map!(a => a.mapWrap!(castToPermissive!RuntimeExpression)).array);
	} else if (values.map!(a => !!a.castToPermissive!PolymorphicExpression).all) {
		return new TupleLitImpl!(TupleLitKind.poly)(values.map!(
				a => a.mapWrap!(castToPermissive!PolymorphicExpression)).array);
	} else {
		return new TupleLitImpl!(TupleLitKind.compile)(values);
	}
}

PolymorphicExpression createTupleLitPoly(E)(Wrapper!E[] values) {
	if (values.map!(a => !!a.castToPermissive!RuntimeExpression).all) {
		return new TupleLitImpl!(TupleLitKind.normal)(
				values.map!(a => a.mapWrap!(castToPermissive!RuntimeExpression)).array);
	} else {
		return new TupleLitImpl!(TupleLitKind.poly)(values.map!(
				a => a.mapWrap!(castToPermissive!PolymorphicExpression)).array);
	}
}

alias If = IfImpl!true;

class IfImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) cond;
	Wrapper!(PickExpression!runtime) yes;
	Wrapper!(PickExpression!runtime) no;
	this(Wrapper!(PickExpression!runtime) cond,
			Wrapper!(PickExpression!runtime) yes, Wrapper!(PickExpression!runtime) no) {
		this.type = yes.type;
		this.cond = cond;
		this.yes = yes;
		this.no = no;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createIf, Pack!(cond, yes, no),
			Pack!(specializeMap, specializeMap, specializeMap));
}

alias createIf = creater!(IfImpl, Pack!(createrRuntimeCheck, createrRuntimeCheck,
		createrRuntimeCheck), Pack!(createrRuntimeMap, createrRuntimeMap, createrRuntimeMap),);

alias While = WhileImpl!true;

class WhileImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) cond;
	Wrapper!(PickExpression!runtime) state;
	this(Wrapper!(PickExpression!runtime) cond, Wrapper!(PickExpression!runtime) state) {
		this.type = new TypeStruct();
		this.cond = cond;
		this.state = state;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createWhile, Pack!(cond, state),
			Pack!(specializeMap, specializeMap));
}

alias createWhile = creater!(WhileImpl, Pack!(createrRuntimeCheck,
		createrRuntimeCheck), Pack!(createrRuntimeMap, createrRuntimeMap),);

alias New = NewImpl!true;

class NewImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) value;
	this(Wrapper!(PickExpression!runtime) value) {
		this.type = new TypePointerImpl!runtime(value.type);
		this.value = value;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createNew, Pack!(value), Pack!(specializeMap));
}

alias createNew = creater!(NewImpl, Pack!(createrRuntimeCheck), Pack!(createrRuntimeMap),);

alias NewArray = NewArrayImpl!true;

class NewArrayImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) length;
	Wrapper!(PickExpression!runtime) value;
	this(Wrapper!(PickExpression!runtime) length, Wrapper!(PickExpression!runtime) value) {
		this.type = new TypeArrayImpl!runtime(value.type);
		this.length = length;
		this.value = value;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createNewArray, Pack!(length, value),
			Pack!(specializeMap, specializeMap));
}

alias createNewArray = creater!(NewArrayImpl, Pack!(createrRuntimeCheck,
		createrRuntimeCheck), Pack!(createrRuntimeMap, createrRuntimeMap),);

alias CastInteger = CastIntegerImpl!true;

class CastIntegerImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) value;
	//todo figure out position data for implicit casts
	this(Wrapper!(PickExpression!runtime) value, Type wanted) {
		this.type = wanted;
		this.value = value;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createCastInteger, Pack!(value, type),
			Pack!(specializeMap, specializeRegular));
}

alias createCastInteger = creater!(IfImpl, Pack!(createrRuntimeCheck,
		createrIgnoreCheck), Pack!(createrRuntimeMap, createrIgnoreMap),);

alias Length = LengthImpl!true;

class LengthImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) value;
	this(Wrapper!(PickExpression!runtime) value) {
		this.type = new TypeInt(0, false);
		this.value = value;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createLength, Pack!(value), Pack!(specializeMap));
}

alias createLength = creater!(LengthImpl, Pack!(createrRuntimeCheck),
		Pack!(createrRuntimeMap),);

alias Index = IndexImpl!true;

class IndexImpl(bool runtime) : PickExpressionLValue!runtime {
	Wrapper!(PickExpression!runtime) array;
	Wrapper!(PickExpression!runtime) index;
	this(PickType!runtime type, Wrapper!(PickExpression!runtime) array,
			Wrapper!(PickExpression!runtime) index) {
		this.type = type;
		this.array = array;
		this.index = index;
	}

	mixin overrideGenericLValue!(runtime);
	mixin overrideSpecialize!(runtime, createIndex, Pack!(type, array, index),
			Pack!(specializeRegular, specializeMap, specializeMap), PolymorphicLValueExpression);
}

alias createIndex = creater!(IndexImpl, Pack!(createrTypeCheck, createrRuntimeCheck, createrRuntimeCheck),
		Pack!(createrTypeMap, createrRuntimeMap, createrRuntimeMap), PolymorphicLValueExpression);

//todo use creater function
PolymorphicExpression createTupleIndex(PolymorphicType type,
		Wrapper!PolymorphicExpression tuple, uint index) {
	if (auto lvalue = tuple.mapWrap!(castTo!PolymorphicLValueExpression)) {
		return createTupleIndexLValue(type, lvalue, index);
	} else {
		return createTupleIndexRValue(type, tuple, index);
	}
}

PolymorphicLValueExpression createTupleIndexLValue(PolymorphicType type,
		Wrapper!PolymorphicLValueExpression tuple, uint index) {
	if (auto runtime = type.castTo!Type) {
		alias TupleIndexRuntime = TupleIndexImpl!true;
		return new TupleIndexRuntime!true(runtime, tuple.mapWrap!(castTo!LValueExpression), index);
	} else {
		alias TupleIndexPoly = TupleIndexImpl!false;
		return new TupleIndexPoly!true(type, tuple, index);
	}
}

PolymorphicExpression createTupleIndexRValue(PolymorphicType type,
		Wrapper!PolymorphicExpression tuple, uint index) {
	if (auto runtime = type.castTo!Type) {
		alias TupleIndexRuntime = TupleIndexImpl!true;
		return new TupleIndexRuntime!false(runtime,
				tuple.mapWrap!(castTo!RuntimeExpression), index);
	} else {
		alias TupleIndexPoly = TupleIndexImpl!false;
		return new TupleIndexPoly!false(type, tuple, index);
	}
}

alias TupleIndex = TupleIndexImpl!true;

template TupleIndexImpl(bool runtime) {
	static if (runtime) {
		alias MaybeLValue = MaybeLValueRuntime;
	} else {
		alias MaybeLValue = MaybeLValuePolymorphic;
		alias PickLValue(bool lvalue : true) = PolymorphicLValueExpression;
		alias PickLValue(bool lvalue : false) = PolymorphicExpression;
	}
	class TupleIndexImpl(bool lvalue) : MaybeLValue!lvalue {
		Wrapper!(MaybeLValue!lvalue) tuple;
		uint index;
		this(PickType!runtime type, Wrapper!(MaybeLValue!lvalue) tuple, uint index) {
			this.type = type;
			this.tuple = tuple;
			this.index = index;
		}

		static if (lvalue) {
			mixin overrideGenericLValue!runtime;
			mixin overrideSpecialize!(runtime, createTupleIndexLValue, Pack!(type, tuple, index),
					Pack!(specializeRegular, specializeMap, specializeIgnore),
					PolymorphicLValueExpression);
		} else {
			mixin overrideGeneric!runtime;
			mixin overrideSpecialize!(runtime, createTupleIndexRValue, Pack!(type, tuple,
					index), Pack!(specializeRegular, specializeMap, specializeIgnore));
		}
	}
}

alias Call = CallImpl!true;

class CallImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) calle;
	Wrapper!(PickExpression!runtime) argument;
	this(PickType!runtime type, Wrapper!(PickExpression!runtime) calle,
			Wrapper!(PickExpression!runtime) argument) {
		this.type = type;
		this.calle = calle;
		this.argument = argument;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createCall, Pack!(type, calle,
			argument), Pack!(specializeRegular, specializeMap, specializeMap));
}

alias createCall = creater!(CallImpl, Pack!(createrTypeCheck, createrRuntimeCheck,
		createrRuntimeCheck), Pack!(createrTypeMap, createrRuntimeMap, createrRuntimeMap),);

alias Slice = SliceImpl!true;

class SliceImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) array;
	Wrapper!(PickExpression!runtime) left;
	Wrapper!(PickExpression!runtime) right;
	this(Wrapper!(PickExpression!runtime) array,
			Wrapper!(PickExpression!runtime) left, Wrapper!(PickExpression!runtime) right) {
		this.type = array.type;
		this.array = array;
		this.left = left;
		this.right = right;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createSlice, Pack!(array, left, right),
			Pack!(specializeMap, specializeMap, specializeMap));
}

alias createSlice = creater!(SliceImpl, Pack!(createrRuntimeCheck, createrRuntimeCheck,
		createrRuntimeCheck), Pack!(createrRuntimeMap, createrRuntimeMap, createrRuntimeMap),);

alias Binary = BinaryImpl!true;

template MaybePolyBinary(string op) {
	template MaybePolyBinary(bool runtime) {
		alias Temp = BinaryImpl!runtime;
		alias MaybePolyBinary = Temp!op;
	}
}

alias createBinary(string op) = creater!(MaybePolyBinary!op, Pack!(createrRuntimeCheck,
		createrRuntimeCheck), Pack!(createrRuntimeMap, createrRuntimeMap),);

template BinaryImpl(bool runtime) {
	class BinaryImpl(string op) : PickExpression!runtime
			if (["*", "/", "%", "+", "-"].canFind(op)) {
		Wrapper!(PickExpression!runtime) left;
		Wrapper!(PickExpression!runtime) right;
		this(Wrapper!(PickExpression!runtime) left, Wrapper!(PickExpression!runtime) right) {
			this.type = left.type;
			this.left = left;
			this.right = right;
		}

		mixin overrideGeneric!runtime;
		mixin overrideSpecialize!(runtime, createBinary!op, Pack!(left,
				right), Pack!(specializeMap, specializeMap));
	}

	class BinaryImpl(string op) : PickExpression!runtime
			if (["~", "==", "!=",
					"<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
		Wrapper!(PickExpression!runtime) left;
		Wrapper!(PickExpression!runtime) right;
		this(Wrapper!(PickExpression!runtime) left, Wrapper!(PickExpression!runtime) right) {
			this.type = new TypeBool;
			this.left = left;
			this.right = right;
		}

		mixin overrideGeneric!runtime;
		mixin overrideSpecialize!(runtime, createBinary!op, Pack!(left,
				right), Pack!(specializeMap, specializeMap));
	}

}

alias Prefix = PrefixImpl!true;

template MaybePolyPrefix(string op) {
	template MaybePolyPrefix(bool runtime) {
		alias Temp = PrefixImpl!runtime;
		alias MaybePolyPrefix = Temp!op;
	}
}

alias createPrefix(string op) = creater!(MaybePolyPrefix!op,
		Pack!(createrRuntimeCheck), Pack!(createrRuntimeMap),);

template PrefixImpl(bool runtime) {

	class PrefixImpl(string op : "-") : PickExpression!runtime {
		Wrapper!(PickExpression!runtime) value;

		this(Wrapper!(PickExpression!runtime) value) {
			this.type = value.type;
			this.value = value;
		}

		mixin overrideGeneric!runtime;
		mixin overrideSpecialize!(runtime, createPrefix!op, Pack!value, Pack!specializeMap);
	}

	class PrefixImpl(string op : "!") : PickExpression!runtime {
		Wrapper!(PickExpression!runtime) value;
		this(Wrapper!(PickExpression!runtime) value) {
			this.type = new TypeBool;
			this.value = value;
		}

		mixin overrideGeneric!runtime;
		mixin overrideSpecialize!(runtime, createPrefix!op, Pack!value, Pack!specializeMap);
	}
}

alias Deref = DerefImpl!true;

class DerefImpl(bool runtime) : PickExpressionLValue!runtime {
	Wrapper!(PickExpression!runtime) value;

	this(PickType!runtime type, Wrapper!(PickExpression!runtime) value) {
		this.type = type;
		this.value = value;
	}

	mixin overrideGenericLValue!runtime;
	mixin overrideSpecialize!(runtime, createDeref, Pack!(type, value),
			Pack!(specializeRegular, specializeMap), PolymorphicLValueExpression);
}

alias createDeref = creater!(DerefImpl, Pack!(createrTypeCheck, createrRuntimeCheck),
		Pack!(createrTypeMap, createrRuntimeMap), PolymorphicLValueExpression);

alias Address = AddressImpl!true;

class AddressImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpressionLValue!runtime) value;
	this(Wrapper!(PickExpressionLValue!runtime) value) {
		this.type = new TypePointerImpl!runtime(value.type);
		this.value = value;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createAddress, Pack!value, Pack!specializeMap);
}

alias createAddress = creater!(AddressImpl, Pack!(createrLValueCheck),
		Pack!(createrLValueMap),);

alias Scope = ScopeImpl!true;

class ScopeImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpression!runtime) pass;
	Wrapper!(PickExpression!runtime) last;
	this(Wrapper!(PickExpression!runtime) pass, Wrapper!(PickExpression!runtime) last) {
		this.type = last.type;
		this.pass = pass;
		this.last = last;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createScope, Pack!(pass, last),
			Pack!(specializeMap, specializeMap));
}

alias createScope = creater!(ScopeImpl, Pack!(createrRuntimeCheck,
		createrRuntimeCheck), Pack!(createrRuntimeMap, createrRuntimeMap),);

alias ScopeVar = ScopeVarImpl!true;

alias ScopeVarImplSuper(bool runtime : true) = AliasSeq!(ScopeVarImpl!false);
alias ScopeVarImplSuper(bool runtime : false) = AliasSeq!();

interface ScopeVarImpl(bool runtime) : PickExpressionLValue!runtime, ScopeVarImplSuper!runtime {
	string nameVirtual();
	final name() {
		return nameVirtual;
	}

	PickExpression!runtime valueNode();
	Position valuePosition();
	final value() {
		return wrapper(valueNode, valuePosition);
	}

	static if (!runtime) {
		override ScopeVarImpl!false specialize(PolymorphicType[PolymorphicVariable] moves,
				Transition transition);
	}
}

class ScopeVarClass(bool runtime) : ScopeVarImpl!runtime {
	string name;
	Wrapper!(PickExpression!runtime) value;

	this(string name, Wrapper!(PickExpression!runtime) value) {
		this.type = value.type;
		this.name = name;
		this.value = value;
	}

override:
	string nameVirtual() {
		return name;
	}

	PickExpression!runtime valueNode() {
		return value;
	}

	Position valuePosition() {
		return value.position;
	}

	mixin overrideGenericLValue!runtime;
	mixin overrideSpecialize!(runtime, createScopeVar, Pack!(name, value),
			Pack!(specializeIgnore, specializeMap), ScopeVarImpl!false);
	static if (runtime) {
		ScopeVarImpl!false specialize(PolymorphicType[PolymorphicVariable] moves,
				Transition transition) {
			return this;
		}
	}
}

alias createScopeVar = creater!(ScopeVarClass, Pack!(createrIgnoreCheck,
		createrRuntimeCheck), Pack!(createrIgnoreMap, createrRuntimeMap), ScopeVarImpl!false);

alias ScopeVarDef = ScopeVarDefImpl!true;

class ScopeVarDefImpl(bool runtime) : PickExpression!runtime {
	ScopeVarImpl!runtime variable;
	Wrapper!(PickExpression!runtime) last;

	this(ScopeVarImpl!runtime variable, Wrapper!(PickExpression!runtime) last) {
		this.type = last.type;
		this.variable = variable;
		this.last = last;
	}

	static void checkParameters(PolymorphicExpression expression,
			PolymorphicType[PolymorphicVariable] moves, Transition transition) {
		if (auto runtime = expression.castTo!(ScopeVarDefImpl!true)) {
			check(isSubSet(runtime.variable.type.parameters, transition.functionVariables),
					"unable to infer type", runtime.variable.value.position);
		} else {
			auto compile = expression.castTo!(ScopeVarDefImpl!false);
			assert(compile);
			check(isSubSet(compile.variable.type.parameters, transition.functionVariables),
					"unable to infer type", compile.variable.value.position);
		}
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createScopeVarDef, Pack!(variable, last),
			Pack!(specializeRegular, specializeMap), PolymorphicExpression, checkParameters);
}

alias createScopeVarDef = creater!(ScopeVarDefImpl, Pack!(castTo!(ScopeVarImpl!true),
		createrRuntimeCheck), Pack!(castTo!(ScopeVarImpl!true), createrRuntimeMap),);

alias Assign = AssignImpl!true;

class AssignImpl(bool runtime) : PickExpression!runtime {
	Wrapper!(PickExpressionLValue!runtime) left;
	Wrapper!(PickExpression!runtime) right;
	Wrapper!(PickExpression!runtime) last;
	this(Wrapper!(PickExpressionLValue!runtime) left,
			Wrapper!(PickExpression!runtime) right, Wrapper!(PickExpression!runtime) last) {
		this.type = last.type;
		this.left = left;
		this.right = right;
		this.last = last;
	}
	//todo this is very hack, replace with something better
	static void checkParameters(PolymorphicExpression expression,
			PolymorphicType[PolymorphicVariable] moves, Transition transition) {
		if (auto runtime = expression.castTo!(AssignImpl!true)) {
			check(isSubSet(runtime.left.type.parameters, transition.functionVariables),
					"unable to infer type", runtime.left.position);
			check(isSubSet(runtime.right.type.parameters, transition.functionVariables),
					"unable to infer type", runtime.right.position);
		} else {
			auto compile = expression.castTo!(AssignImpl!false);
			assert(compile);
			check(isSubSet(compile.left.type.parameters, transition.functionVariables),
					"unable to infer type", compile.left.position);
			check(isSubSet(compile.right.type.parameters, transition.functionVariables),
					"unable to infer type", compile.right.position);
		}
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createAssign, Pack!(left, right, last),
			Pack!(specializeMap, specializeMap, specializeMap),
			PolymorphicExpression, checkParameters);
}

alias createAssign = creater!(AssignImpl, Pack!(createrLValueCheck, createrRuntimeCheck,
		createrRuntimeCheck), Pack!(createrLValueMap, createrRuntimeMap, createrRuntimeMap));

alias FunctionLiteral = FunctionLiteralImpl!true;

alias MaybeSymbol(bool runtime : true) = Symbol;
alias MaybeSymbol(bool runtime : false) = AliasSeq!();

class FunctionLiteralImpl(bool runtime) : PickExpression!runtime, MaybeSymbol!runtime {
	Wrapper!(PickExpression!runtime) text;
	bool explicitInfer;

	static if (!runtime) {
		string name;
	}
	this(PickType!runtime type, string name, bool explicitInfer) {
		this.type = type;
		this.explicitInfer = explicitInfer;
		static if (runtime) {
			if (explicitInfer) {
				this.name = name;
			} else {
				this.name = name ~ "_" ~ type.mangle;
			}
		} else {
			this.name = name;
		}
	}

	this(PickType!runtime type, Wrapper!(PickExpression!runtime) text,
			string name, bool explicitInfer) {
		assert(!runtime);
		this.type = type;
		this.text = text;
		this.name = name;
		this.explicitInfer = explicitInfer;
	}

	mixin overrideGeneric!runtime;
	void specializePostfix(PolymorphicExpression result,
			PolymorphicType[PolymorphicVariable] moves, Transition transition) {
		auto vars = transition.functionVariables;
		transition.functionVariables = result.type.parameters;
		if (auto runtime = result.castTo!(FunctionLiteralImpl!true)) {
			runtime.text = text.mapWrap!(a => a.specialize(moves, transition)
					.castTo!RuntimeExpression);
			assert(runtime.text, "null text:" ~ text.to!string);
			transition.source.exports[name] = runtime;
		} else {
			auto compile = result.castTo!(FunctionLiteralImpl!false);
			compile.text = text.mapWrap!(a => a.specialize(moves, transition));
		}
		transition.functionVariables = vars;
	}

	mixin overrideSpecialize!(runtime, createFunctionLiteral, Pack!(type,
			name, explicitInfer), Pack!(specializeRegular,
			specializeIgnore, specializeIgnore), PolymorphicExpression, specializePostfix);
	static if (runtime) {
		mixin overrideSymbol;
	}
}

alias createFunctionLiteral = creater!(FunctionLiteralImpl, Pack!(createrTypeCheck, createrIgnoreCheck,
		createrIgnoreCheck), Pack!(createrTypeMap, createrIgnoreMap, createrIgnoreMap));

alias FuncArgument = FuncArgumentImpl!true;

class FuncArgumentImpl(bool runtime) : PickExpression!runtime {
	this(PickType!runtime type) {
		this.type = type;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createFuncArgument, Pack!type, Pack!specializeRegular);
}

alias createFuncArgument = creater!(FuncArgument, Pack!(createrTypeCheck),
		Pack!(createrTypeMap));

class StringLit : RuntimeExpression {
	string value;
	this(string value) {
		this.type = new TypeArray(new TypeChar());
		this.value = value;
	}

	mixin overrideRuntime;
}

alias ArrayLit = ArrayLitImpl!true;

class ArrayLitImpl(bool runtime) : PickExpression!runtime {
	Wrapper!((PickExpression!runtime))[] values;
	this(PickType!runtime type, Wrapper!(PickExpression!runtime)[] values) {
		this.type = type;
		this.values = values;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createArrayLit, Pack!(type, values),
			Pack!(specializeRegular, specializeMapList));
}

alias createArrayLit = creater!(ArrayLitImpl, Pack!(createrTypeCheck,
		createrRuntimeListCheck), Pack!(createrTypeMap, createrRuntimeListMap));

alias ExternJs = ExternJsImpl!true;

class ExternJsImpl(bool runtime) : PickExpression!runtime {
	string name;
	this(PickType!runtime type, string name) {
		this.type = type;
		this.name = name;
	}

	mixin overrideGeneric!runtime;
	mixin overrideSpecialize!(runtime, createExternJs, Pack!(type, name),
			Pack!(specializeRegular, specializeIgnore));
}

alias createExternJs = creater!(ExternJs, Pack!(createrTypeCheck,
		createrIgnoreCheck), Pack!(createrTypeMap, createrIgnoreMap),);

interface Symbol {
	final string name() {
		return nameVirtual();
	}

	string nameVirtual();

	JsExpr generateSymbol(JsScope, Extra*);
}

mixin template overrideSymbol() {
	string name;
	override string nameVirtual() {
		return name;
	}

	override JsExpr generateSymbol(JsScope depend, Extra* extra) {
		return generateSymbolImpl(this, depend, extra);
	}
}

struct ModuleAlias {
	Wrapper!Expression element;
	bool visible;
}

class Module {
	ModuleAlias[string] aliases;
	Symbol[string] exports;
	Parser.ModuleVarDef[string] rawSymbols;
}

class ModuleVarDef : Symbol {
	Wrapper!RuntimeExpression value;
	bool visible;
	this(Wrapper!RuntimeExpression value, bool visible, string name) {
		this.value = value;
		this.visible = visible;
		this.name = name;
	}

	mixin overrideSymbol;
}

abstract class CompileTimeType : Expression {
	this() {
		this.type = metaclass;
	}

	mixin overrideExpression;

	override string toString();
}

abstract class PolymorphicType : CompileTimeType {
	Tuple!()[PolymorphicVariable] parameters();
	PolymorphicType specialize(PolymorphicType[PolymorphicVariable] moves, Transition transition);
}

class PolymorphicVariable : PolymorphicType {
	override Tuple!()[PolymorphicVariable] parameters() {
		return [this: tuple()];
	}

	override PolymorphicType specialize(PolymorphicType[PolymorphicVariable] moves,
			Transition transition) {
		if (this in moves) {
			return moves[this];
		} else {
			return this;
		}
	}

	override string toString() {
		return (cast(void*) this).to!string;
	}
}

abstract class Type : PolymorphicType {
	string mangle();
	override Tuple!()[PolymorphicVariable] parameters() {
		return null;
	}

	override PolymorphicType specialize(PolymorphicType[PolymorphicVariable] moves,
			Transition transition) {
		return this;
	}
}

class TypeBool : Type {
	override string mangle() {
		return "boolean";
	}

	override string toString() {
		return "boolean";
	}
}

class TypeChar : Type {
	override string mangle() {
		return "character";
	}

	override string toString() {
		return "character";
	}
}

class TypeInt : Type {
	uint size;
	bool signed;
	this(int size, bool signed = true) {
		this.size = size;
		this.signed = signed;
	}

	override string mangle() {
		return (signed ? "integer" : "natural") ~ size.to!string;
	}

	override string toString() {
		return (signed ? "integer " : "natural ") ~ size.to!string;
	}
}

TypeMetaclass metaclass;
static this() {
	metaclass = new TypeMetaclass();
}

alias TypeStruct = TypeStructImpl!(TupleLitKind.normal);

alias PickType(TupleLitKind kind : TupleLitKind.normal) = Type;
alias PickType(TupleLitKind kind : TupleLitKind.poly) = PolymorphicType;
alias PickType(TupleLitKind kind : TupleLitKind.compile) = CompileTimeType;
alias PickType(bool poly : false) = PolymorphicType;
alias PickType(bool poly : true) = Type;

class TypeStructImpl(TupleLitKind kind) : PickType!kind {
	PickType!kind[] values;
	this() {
		this([]);
	}

	this(PickType!kind[] values) {
		this.values = values;
	}

	static if (kind == TupleLitKind.normal) {
		override string mangle() {
			if (values.length == 0) {
				return "void";
			}
			return "tuple_of_" ~ values[0 .. $ - 1].map!(a => a.mangle ~ "_and_")
				.joiner
				.to!string ~ values[$ - 1].mangle ~ "_end";
		}
	}

	static if (kind == TupleLitKind.poly) {
		override Tuple!()[PolymorphicVariable] parameters() {
			return values.map!(a => a.parameters.keys).joiner.array.arrayToSet;
		}

		override PolymorphicType specialize(PolymorphicType[PolymorphicVariable] moves,
				Transition transition) {
			return createTypeStruct(values.map!(a => a.specialize(moves, transition)).array);
		}
	}

	override string toString() {
		return "(" ~ values.map!(a => a.toString ~ ",")
			.joiner
			.array
			.to!string ~ ")";
	}
}

PolymorphicType createTypeStruct(E)(E[] values) {
	if (values.map!(a => !!a.castToPermissive!Type).all) {
		return new TypeStructImpl!(TupleLitKind.normal)(
				values.map!(a => a.castToPermissive!Type).array);
	} else {
		return new TypeStructImpl!(TupleLitKind.poly)(
				values.map!(a => a.castToPermissive!PolymorphicType).array);
	}
}

alias TypeArray = TypeArrayImpl!true;

class TypeArrayImpl(bool runtime) : PickType!runtime {
	PickType!runtime array;

	this(PickType!runtime array) {
		this.array = array;
	}

	static if (runtime) {
		override string mangle() {
			return array.mangle ~ "_array";
		}
	} else {
		override Tuple!()[PolymorphicVariable] parameters() {
			return array.parameters;
		}

		override PolymorphicType specialize(PolymorphicType[PolymorphicVariable] moves,
				Transition transition) {
			return createTypeArray(array.specialize(moves, transition));
		}
	}

	override string toString() {
		return array.toString() ~ "[]";
	}
}

alias createTypeArray = creater!(TypeArrayImpl, Pack!(createrTypeCheck),
		Pack!(createrTypeMap), PolymorphicType);

alias TypeFunction = TypeFunctionImpl!true;

class TypeFunctionImpl(bool runtime) : PickType!runtime {
	PickType!runtime result;
	PickType!runtime argument;

	this(PickType!runtime result, PickType!runtime argument) {
		this.result = result;
		this.argument = argument;
	}

	static if (runtime) {
		override string mangle() {
			return "function_of_" ~ result.mangle ~ "_to_" ~ argument.mangle ~ "_end";
		}
	} else {
		override Tuple!()[PolymorphicVariable] parameters() {
			return arrayToSet(result.parameters.keys ~ argument.parameters.keys);
		}

		override PolymorphicType specialize(PolymorphicType[PolymorphicVariable] moves,
				Transition transition) {
			return createTypeFunction(result.specialize(moves, transition),
					argument.specialize(moves, transition));
		}
	}

	override string toString() {
		return argument.toString ~ "->" ~ result.toString;
	}
}

alias createTypeFunction = creater!(TypeFunction, Pack!(createrTypeCheck,
		createrTypeCheck), Pack!(createrTypeMap, createrTypeMap), PolymorphicType);

alias TypePointer = TypePointerImpl!true;

class TypePointerImpl(bool runtime) : PickType!runtime {
	PickType!runtime value;

	this(PickType!runtime value) {
		this.value = value;
	}

	static if (runtime) {
		override string mangle() {
			return value.mangle ~ "_pointer";
		}
	} else {
		override Tuple!()[PolymorphicVariable] parameters() {
			return value.parameters;
		}

		override PolymorphicType specialize(PolymorphicType[PolymorphicVariable] moves,
				Transition transition) {
			return createTypePointer(value.specialize(moves, transition));
		}
	}

	override string toString() {
		return value.toString() ~ "(*)";
	}
}

alias createTypePointer = creater!(TypePointerImpl, Pack!(createrTypeCheck),
		Pack!(createrTypeMap), PolymorphicType);

struct Subsitution {
	PolymorphicVariable from;
	PolymorphicType to;
}

alias PolyTypes = AliasSeq!(TypeBool, TypeChar, TypeInt, TypeStructImpl!(TupleLitKind.normal),
		TypeStructImpl!(TupleLitKind.poly), TypePointerImpl!true,
		TypePointerImpl!false, TypeArrayImpl!true, TypeArrayImpl!false,
		TypeFunctionImpl!true, TypeFunctionImpl!false, PolymorphicVariable);
//todo use virtual table dispatch for this
Subsitution[] typeMatch(PolymorphicType a, PolymorphicType b, Position position) {
	return dispatch!((a, b) => dispatch!((a, b) => typeMatchImpl(b, a, position), PolyTypes)(b, a),
			PolyTypes)(a, b);
}

Subsitution[] typeMatchImpl(T1, T2)(T1 left, T2 right, Position position) {
	if (left is right) {
		return [];
	}
	static if (is(T1 == PolymorphicVariable)) {
		return [Subsitution(left, right)];
	} else static if (is(T2 == PolymorphicVariable)) {
		return [Subsitution(right, left)];
	} else static if (is(T1 == TypeBool) && is(T2 == TypeBool)) {
		return [];
	} else static if (is(T1 == TypeChar) && is(T2 == TypeChar)) {
		return [];
	} else static if (is(T1 == TypeInt) && is(T2 == TypeInt)) {
		if (left.size == right.size) {
			return [];
		}
	} else static if (is(T1 == TypeStructImpl!a, TupleLitKind a)
			&& is(T2 == TypeStructImpl!b, TupleLitKind b)) {
		if (left.values.length == right.values.length) {
			return zip(left.values, right.values).map!(a => typeMatch(a.expand,
					position)).joiner.array;
		}
	} else static if (is(T1 == TypeArrayImpl!a, bool a) && is(T2 == TypeArrayImpl!b, bool b)) {
		return typeMatch(left.array, right.array, position);
	} else static if (is(T1 == TypeFunctionImpl!a, bool a) && is(T2 == TypeFunctionImpl!b, bool b)) {
		return typeMatch(left.result, right.result, position) ~ typeMatch(left.argument,
				right.argument, position);
	} else static if (is(T1 == TypePointerImpl!a, bool a) && is(T2 == TypePointerImpl!b, bool b)) {
		return typeMatch(left.value, right.value, position);
	}
	error("Can't match " ~ left.toString ~ " to " ~ right.toString, position);
	assert(0);
}

//dark corners
class TypeMetaclass : CompileTimeType {
	this() {
	}

	override string toString() {
		return "metaclass";
	}
}

class TypeImport : CompileTimeType {
	override string toString() {
		return "import";
	}
}

//curried cast ie cast(int)
class TypeCastPartial : CompileTimeType {
	override string toString() {
		return "castpartial";
	}
}

class TypeInferPartial : CompileTimeType {
	override string toString() {
		return "inferpartial";
	}
}

class TypeGenericFunction : CompileTimeType {
	override string toString() {
		return "generic";
	}
}

alias Types = AliasSeq!(TypeBool, TypeChar, TypeInt, TypeStruct, TypePointer,
		TypeArray, TypeFunction);
//todo use virtual table dispatch for this
bool sameType(Type a, Type b) {
	return dispatch!((a, b) => dispatch!((a, b) => sameTypeImpl(b, a), Types)(b, a), Types)(a, b);
}

bool sameTypeImpl(T1, T2)(T1 a, T2 b) {
	static if (!is(T1 == T2)) {
		return false;
	} else {
		return sameTypeImpl2(a, b);
	}
}

bool sameTypeImpl2(T)(T a, T b) if (is(T == TypeBool) || is(T == TypeChar)) {
	return true;
}

bool sameTypeImpl2(TypeInt a, TypeInt b) {
	return a.size == b.size;
}

bool sameTypeImpl2(TypeStruct a, TypeStruct b) {
	return a.values.length == b.values.length && zip(a.values, b.values)
		.map!(a => sameType(a[0], a[1])).all;
}

bool sameTypeImpl2(TypePointer a, TypePointer b) {
	return sameType(a.value, b.value);
}

bool sameTypeImpl2(TypeArray a, TypeArray b) {
	return sameType(a.array, b.array);
}

bool sameTypeImpl2(TypeFunction a, TypeFunction b) {
	return sameType(a.result, b.result) && sameType(a.argument, b.argument);
}
