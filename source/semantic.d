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
module semantic;
import std.algorithm : all, any, canFind, each, filter, map, reduce, until;
import std.array : join, array;
import std.bigint : BigInt;
import std.conv : to;
import std.file : read;
import std.meta : AliasSeq;
import std.range : drop, take;

import ast;
import error : error, Position;
import parser;

void processModule(Module mod) {
	mod.process = true;
	auto trace = Trace(mod, null);
	foreach (symbol; mod.symbols) {
		if (!symbol.process) {
			semantic1(symbol, &trace);
		}
		if (!symbol.ispure) {
			error("Impure expression in global", symbol.pos);
		}
	}
}

Bool isBool(Expression type) {
	return cast(Bool) type;
}

Char isChar(Expression type) {
	return cast(Char) type;
}

Int isInt(Expression type) {
	return cast(Int) type;
}

UInt isUInt(Expression type) {
	return cast(UInt) type;
}

Postfix!"(*)" isPointer(Expression type) {
	return cast(Postfix!"(*)") type;
}

//todo remove these
ArrayIndex isArray(Expression type) {
	if (type.isType && cast(ArrayIndex) type) {
		return cast(ArrayIndex) type;
	}
	return null;
}

FCall isFunction(Expression type) {
	if (type.isType && cast(FCall) type) {
		return cast(FCall) type;
	}
	return null;
}

bool isExtern(Expression expression) {
	if (auto ext = cast(Cast) expression) {
		return !!cast(ExternJS) ext.value;
	}
	return !!cast(ExternJS) expression;
}

ref Expression[] values(Struct stru) {
	auto tuple = cast(TupleLit) stru.value;
	assert(tuple);
	return tuple.values;
}

bool isType(Expression expression) {
	expression = expression;
	return !!cast(Metaclass) expression.type;
}

bool isRuntimeValue(Expression expression) {
	expression = expression;
	return !(expression.isType || cast(Import) expression);
}

void checkRuntimeValue(Expression expression) {
	if (!isRuntimeValue(expression)) {
		error("Expected runtime value", expression.pos);
	}
}

//makes sure expression is a type or implicitly convert it to a type
void checkType(ref Expression expression) {
	if (auto tuple = cast(TupleLit) expression) {
		auto structWrap = new Struct;
		structWrap.value = expression;
		expression = structWrap;
		expression.type = metaclass;
	}
	if (!isType(expression)) {
		error("Expected type", expression.pos);
	}
}

Expression createType(T, Args...)(Args args) {
	auto type = createTypeImpl!T(args);
	semantic1Head(type);
	return type;
}

T createTypeImpl(T)()
		if (is(T == Bool) || is(T == Char) || is(T == ImportType) || is(T == ExternType)) {
	auto type = new T;
	semantic1Head(type);
	return type;
}

T createTypeImpl(T)(int size) if (is(T == Int) || is(T == UInt)) {
	auto type = new T;
	type.size = size;
	semantic1Head(type);
	return type;
}

T createTypeImpl(T)(Expression value) if (is(T == Postfix!"(*)")) {
	auto type = new T;
	type.value = value;
	semantic1Head(type);
	return type;
}

T createTypeImpl(T)(Expression[] values = null) if (is(T == Struct)) {
	auto type = new T;
	auto tuple = new TupleLit();
	tuple.values = values;
	semantic1Head(tuple);
	type.value = tuple;
	semantic1Head(type);
	return type;
}

T createTypeImpl(T)(Expression fptr, Expression arg) if (is(T == FCall)) {
	auto type = new T;
	type.fptr = fptr;
	type.arg = arg;
	semantic1Head(type);
	return type;
}

T createTypeImpl(T)(Expression array) if (is(T == ArrayIndex)) {
	auto type = new T;
	type.array = array;
	type.index = createType!Struct();
	semantic1Head(type);
	return type;
}

//used in semantic1 and creating types
//process certain expressions with out recursing
void semantic1Head(T)(T that) {
	semantic1HeadImpl(that);
	that.type = metaclass;
	that.ispure = true;
	that.process = true;
}

void semantic1Head(TupleLit that) {
	if (that.values.map!(a => !!cast(Metaclass) a).all) {
		auto cycle = new Struct();
		cycle.value = that;
		semantic1Head(cycle);
		that.type = cycle;
	} else {
		that.type = createType!Struct(that.values.map!(a => a.type).array);
	}
	that.ispure = that.values.map!(a => a.ispure).all;
}

void semantic1HeadImpl(T)(T that)
		if (is(T == Bool) || is(T == Char) || is(T == ImportType) || is(T == ExternType)) {
}

void semantic1HeadImpl(T)(T that) if (is(T == Int) || is(T == UInt)) {
	if (that.size == 0) {
		return;
	}
	uint check = 1;
	while (true) {
		if (check == that.size) {
			return;
		}
		if (check > that.size) {
			error("Bad Int Size", that.pos);
		}
		check *= 2;
	}
}

void semantic1HeadImpl(T)(T that) if (is(T == Postfix!"(*)")) {
	checkType(that.value);
}

void semantic1HeadImpl(T)(T that) if (is(T == Struct)) {
	if (!cast(TupleLit) that.value) {
		error("expected tuple lit after struct", that.pos);
	}
	that.values.each!checkType;
}

void semantic1HeadImpl(T)(T that) if (is(T == FCall)) {
	checkType(that.fptr);
	checkType(that.arg);
}

void semantic1HeadImpl(T)(T that) if (is(T == ArrayIndex)) {
	checkType(that.index);
	if (!sameType(that.index, createType!Struct())) {
		error("Expected empty type in array type", that.pos);
	}
}

void semantic1(ref Statement that, Trace* trace) {
	dispatch!(semantic1, VarDef, Expression, Assign)(that, trace);
}

void semantic1(VarDef that, Trace* trace) {
	semantic1(that.definition, trace);
	that.ispure = that.definition.ispure;
	if (!that.manifest) {
		that.ispure = false;
		checkRuntimeValue(that.definition);
	}
	if (that.explicitType) {
		semantic1(that.explicitType, trace);
		checkType(that.explicitType);
		if (!sameTypeValueType(that.definition, that.explicitType)) {
			error("types don't match", that.pos);
		}
	}
	if (auto scopeVar = cast(ScopeVarDef) that) {
		if (!that.manifest) {
			scopeVar.func = trace.range.map!(a => a.node)
				.map!(a => cast(FuncLit) a).filter!(a => !!a).front;
		}
	}
	if (auto moduleVar = cast(ModuleVarDef) that) {
		if (!that.manifest) {
			auto mod = cast(Module) trace.range.reduce!"b".node;
			mod.exports[that.name] = Symbol(moduleVar);
		}
	}
}

void semantic1(Assign that, Trace* trace) {
	semantic1(that.left, trace);
	semantic1(that.right, trace);
	if (!(sameType(that.left.type, that.right.type) || implicitConvert(that.right, that.left.type))) {
		error("= only works on the same type", that.pos);
	}
	if (!that.left.lvalue) {
		error("= only works on lvalues", that.pos);
	}
	that.ispure = that.left.ispure && that.right.ispure;
}

void semantic1(ref Expression that, Trace* trace) {
	if (that.process) {
		error("Cyclic variable", that.pos);
	}
	that.process = true;
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	dispatch!(semantic1ExpressionImpl, Metaclass, Bool, Char, Int, UInt, Postfix!"(*)",
			Import, IntLit, CharLit, BoolLit, Struct, TupleLit, FuncArgument, If,
			While, New, NewArray, Cast, ArrayIndex, FCall, Slice, Scope, FuncLit,
			StringLit, ArrayLit, ExternJS, Binary!"*", Binary!"/",
			Binary!"%", Binary!"+", Binary!"-", Binary!"~", Binary!"==",
			Binary!"!=", Binary!"<=", Binary!">=", Binary!"<", Binary!">",
			Binary!"&&", Binary!"||", Prefix!"+", Prefix!"-", Prefix!"*",
			Prefix!"/", Prefix!"&", Prefix!"!", Expression)(that, trace);
	assert(that.type);
	assert(that.type.isType);
	assert(!cast(Variable) that);
}
//for types that cases that requre ast modification
void semantic1ExpressionImpl(ref Expression that, Trace* trace) {
	dispatch!(semantic1ExpressionImplWritable, Variable, Dot)(that, trace, that);
}
//bug variable still in ast after this pass
void semantic1ExpressionImplWritable(Variable that, Trace* trace, ref Expression output) {
	Trace subTrace;
	auto source = trace.search(that.name, subTrace);
	if (source is null) {
		error("Unknown variable", that.pos);
	}

	if (source.definition.type is null) {
		semantic1(source.definition, &subTrace);
	}
	Expression thealias;
	if (source.manifest) {
		thealias = source.definition;
	} else {
		if (auto scopeDef = cast(ScopeVarDef) source) {
			auto scopeRef = new ScopeVarRef();
			scopeRef.definition = scopeDef;
			scopeRef.ispure = true;
			scopeRef.type = source.type;
			scopeRef.lvalue = true;
			thealias = scopeRef;
		} else if (auto moduleDef = cast(ModuleVarDef) source) {
			auto moduleRef = new ModuleVarRef();
			moduleRef.definition = moduleDef;
			moduleRef.ispure = false;
			moduleRef.type = source.type;
			moduleRef.lvalue = true;
			thealias = moduleRef;
		} else {
			assert(0);
		}
	}
	assert(thealias.type);
	if (auto scopeVarRef = cast(ScopeVarRef) thealias) {
		checkNotClosure(scopeVarRef, trace, that.pos);
	}
	output = thealias;
}

void checkNotClosure(ScopeVarRef that, Trace* trace, Position pos) {
	auto funcRange = trace.range.map!(a => a.node).map!(a => cast(FuncLit) a).filter!(a => !!a);
	if (funcRange.empty) {
		assert(0); //this should never happen
	}
	if (funcRange.front !is that.definition.func) {
		error("Closures not supported", pos);
	}
}

void semantic1ExpressionImplWritable(Dot that, Trace* trace, ref Expression output) {
	semantic1(that.value, trace);
	semantic1Dot(that.value.type, trace, that, output);
	that.ispure = that.value.ispure;
}

void semantic1Dot(Expression that, Trace* trace, Dot dot, ref Expression output) {
	dispatch!(semantic1DotImpl, Struct, ArrayIndex, ImportType, Expression)(that,
			trace, dot, output);
}

void semantic1DotImpl(T)(T that, Trace* trace, Dot dot, ref Expression output) {
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	static if (is(T == Struct)) {
		auto index = dot.index;
		uint typeIndex = index.get!(BigInt).toInt;
		if (typeIndex >= that.values.length) {
			error("Index number to high", dot.pos);
		}
		dot.type = that.values[typeIndex];
		dot.lvalue = dot.value.lvalue;
	} else static if (is(T == ArrayIndex)) {
		auto index = dot.index;
		if (!(index.peek!string && index.get!string == "length")) {
			semantic1DotImpl!Expression(that, trace, dot, output);
			return;
		}
		dot.type = createType!UInt(0);
	} else static if (is(T == ImportType)) {
		if (dot.index.peek!BigInt) {
			error("attempting to index a module with an integer", that.pos);
		}
		auto imp = cast(Import) dot.value;
		auto name = dot.index.get!string;
		if (!(name in imp.mod.symbols)) {
			error(name ~ " doesn't exist in module", dot.pos);
		}
		auto definition = imp.mod.symbols[name];
		if (!definition.visible) {
			error(name ~ " is not visible", dot.pos);
		}
		ModuleVarRef thealias = new ModuleVarRef();
		thealias.definition = definition;
		thealias.ispure = false;
		thealias.type = definition.type;
		thealias.lvalue = true;
		if (definition.type is null) {
			auto definitionTrace = Trace(imp.mod, null);
			semantic1(thealias.definition, &definitionTrace);
		}
		output = thealias;
	} else static if (is(T == Expression)) {
		error("Unable to dot", that.pos);
	} else {
		pragma(msg, T);
		static assert(0);
	}
}

Metaclass metaclass;
static this() {
	metaclass = new Metaclass();
	metaclass.type = metaclass;
	metaclass.ispure = true;
}

void semantic1ExpressionImpl(Metaclass that, Trace* trace) {
}

void semantic1ExpressionImpl(Import that, Trace* trace) {
	that.type = createType!ImportType;
	that.ispure = true;
}

void semantic1ExpressionImpl(T)(T that, Trace* trace)
		if (is(T == Bool) || is(T == Char) || is(T == Int) || is(T == UInt)) {
	semantic1Head(that);
}

void semantic1ExpressionImpl(T)(T that, Trace* trace) if (is(T == Postfix!"(*)")) {
	semantic1(that.value, trace);
	semantic1Head(that);
}

void semantic1ExpressionImpl(IntLit that, Trace* trace) {
	if (that.usigned) {
		that.type = createType!UInt(0);
	} else {
		that.type = createType!Int(0);
	}
	that.ispure = true;
}

void semantic1ExpressionImpl(CharLit that, Trace* trace) {
	that.type = createType!Char;
	that.ispure = true;
}

void semantic1ExpressionImpl(BoolLit that, Trace* trace) {
	that.type = createType!Bool;
	that.ispure = true;
}

void semantic1ExpressionImpl(Struct that, Trace* trace) {
	semantic1(that.value, trace);
	semantic1Head(that);
}

void semantic1ExpressionImpl(TupleLit that, Trace* trace) {
	foreach (value; that.values) {
		semantic1(value, trace);
	}

	semantic1Head(that);
}

void semantic1ExpressionImpl(FuncArgument that, Trace* trace) {
	foreach (node; trace.range.map!(a => a.node)) {
		if (auto func = cast(FuncLit) node) {
			that.func = func;
			that.type = func.argument;
			//todo make lvalue-able
			return;
		}
	}
	error("$@ without function", that.pos);
}

void semantic1ExpressionImpl(If that, Trace* trace) {
	semantic1(that.cond, trace);
	semantic1(that.yes, trace);
	semantic1(that.no, trace);
	if (!that.cond.type.isBool) {
		error("Boolean expected in if expression", that.cond.pos);
	}
	if (!sameTypeValueValue(that.yes, that.no)) {
		error("If expression with the true and false parts having different types", that.pos);
	}
	that.type = that.yes.type;
	that.ispure = that.cond.ispure && that.yes.ispure && that.no.ispure;
}

void semantic1ExpressionImpl(While that, Trace* trace) {
	semantic1(that.cond, trace);
	semantic1(that.state, trace);
	if (!that.cond.type.isBool) {
		error("Boolean expected in while expression", that.cond.pos);
	}
	that.type = createType!Struct();
	that.ispure = that.cond.ispure && that.state.ispure;
}

void semantic1ExpressionImpl(New that, Trace* trace) {
	semantic1(that.value, trace);
	that.type = createType!(Postfix!"(*)")(that.value.type);
	that.ispure = that.value.ispure;
}

void semantic1ExpressionImpl(NewArray that, Trace* trace) {
	semantic1(that.length, trace);
	semantic1(that.value, trace);
	if (!sameTypeValueType(that.length, createType!UInt(0))) {
		error("Can only create an array with length of UInts", that.length.pos);
	}
	that.type = createType!ArrayIndex(that.value.type);
	that.ispure = that.length.ispure && that.value.ispure;
}

void semantic1ExpressionImpl(Cast that, Trace* trace) {
	semantic1(that.value, trace);
	semantic1(that.wanted, trace);
	checkType(that.wanted);
	if (!castable(that.value.type, that.wanted)) {
		error("Unable to cast", that.pos);
	}
	that.type = that.wanted;
	that.ispure = that.value.ispure;
}

void semantic1ExpressionImpl(ArrayIndex that, Trace* trace) {
	semantic1(that.array, trace);
	semantic1(that.index, trace);
	if (that.array.isType) {
		semantic1Head(that);
	} else {
		if (!that.array.type.isArray) {
			error("Unable able to index", that.pos);
		}
		if (!sameTypeValueType(that.index, createType!UInt(0))) {
			error("Can only index an array with UInts", that.pos);
		}
		auto arrayType = that.array.type.isArray;
		that.type = arrayType.array;
		that.lvalue = true;
		that.ispure = that.array.ispure && that.index.ispure;
	}
}

void semantic1ExpressionImpl(FCall that, Trace* trace) {
	semantic1(that.fptr, trace);
	semantic1(that.arg, trace);
	if (that.fptr.isType || that.arg.isType) {
		semantic1Head(that);
	} else {
		auto fun = that.fptr.type.isFunction;
		if (!fun) {
			error("Not a function", that.pos);
		}
		if (!sameTypeValueType(that.arg, fun.arg)) {
			error("Unable to call function with the  argument's type", that.pos);
		}
		that.type = fun.fptr;
		that.ispure = that.fptr.ispure && that.arg.ispure /* todo fix me && fun.ispure*/ ;
	}
}

void semantic1ExpressionImpl(Slice that, Trace* trace) {
	semantic1(that.array, trace);
	semantic1(that.left, trace);
	semantic1(that.right, trace);
	if (!that.array.type.isArray) {
		error("Not an array", that.pos);
	}
	if (!(sameTypeValueType(that.right, createType!UInt(0))
			&& sameTypeValueType(that.left, createType!UInt(0)))) {
		error("Can only index an array with UInts", that.pos);
	}
	that.type = that.array.type;
	that.ispure = that.array.ispure && that.left.ispure && that.right.ispure;
}

void semantic1ExpressionImpl(string op)(Binary!op that, Trace* trace) {
	semantic1(that.left, trace);
	semantic1(that.right, trace);
	static if (["*", "/", "%", "+", "-", "<=", ">=", ">", "<"].canFind(op)) {
		auto ty = that.left.type;
		if (!((ty.isUInt || ty.isInt) && (sameTypeValueValue(that.left, that.right)))) {
			error(op ~ " only works on Ints or UInts of the same Type", that.pos);
		}
		static if (["<=", ">=", ">", "<"].canFind(op)) {
			that.type = createType!Bool;
		} else {
			that.type = ty;
		}
		that.ispure = that.left.ispure && that.right.ispure;
	} else static if (op == "~") {
		auto ty = that.left.type;
		if (!ty.isArray && sameType(ty, that.right.type)) {
			error("~ only works on Arrays of the same Type", that.pos);
		}
		that.type = ty;
		that.ispure = that.left.ispure && that.right.ispure;
	} else static if (["==", "!="].canFind(op)) {
		if (!(sameTypeValueValue(that.left, that.right))) {
			error(op ~ " only works on the same Type", that.pos);
		}
		that.type = createType!Bool;
		that.ispure = that.left.ispure && that.right.ispure;
	} else static if (["&&", "||"].canFind(op)) {
		auto ty = that.left.type;
		if (!(ty.isBool && sameType(ty, that.right.type))) {
			error(op ~ " only works on Bools", that.pos);
		}
		that.type = createType!Bool;
		that.ispure = that.left.ispure && that.right.ispure;
	} else {
		static assert(0);
	}
}

void semantic1ExpressionImpl(string op)(Prefix!op that, Trace* trace) {
	semantic1(that.value, trace);
	static if (op == "-") {
		if (!that.value.type.isInt) {
			error("= only works Signed Ints", that.pos);
		}
		that.type = that.value.type;
		that.ispure = that.value.ispure;
	} else static if (op == "*") {
		if (!that.value.type.isPointer) {
			error("* only works on pointers", that.pos);
		}
		that.type = that.value.type.isPointer.value;
		that.lvalue = true;
		that.ispure = that.value.ispure;
	} else static if (op == "&") {
		if (!that.value.lvalue) {
			error("& only works lvalues", that.pos);
		}

		static void assignHeapImpl(T)(T that, Trace* trace) {
			auto nextTrace = Trace(that, trace);
			trace = &nextTrace;
			static if (is(T == ScopeVarRef) || is(T == ModuleVarRef)) {
				that.definition.heap = true;
			} else static if (is(T == Dot)) {
				assignHeap(that.value, trace);
			}
		}

		static void assignHeap(Expression that, Trace* trace) {
			return dispatch!(assignHeapImpl, ScopeVarRef, ModuleVarRef, Dot, Expression)(that,
					trace);
		}

		assignHeap(that.value, trace);

		that.type = createType!(Postfix!"(*)")(that.value.type);
		that.ispure = that.value.ispure;
	} else static if (op == "!") {
		if (!that.value.type.isBool) {
			error("! only works on Bools", that.pos);
		}
		that.type = that.value.type;
		that.ispure = that.value.ispure;
	} else static if (["+", "/"].canFind(op)) {
		error(op ~ " not supported", that.pos);
	} else {
		static assert(0);
	}
}

void semantic1ExpressionImpl(Scope that, Trace* trace) {
	that.ispure = true;
	foreach (symbol; that.symbols) {
		semantic1(symbol, trace);
	}
	foreach (state; that.states) {
		semantic1(state, trace);
		trace.context.pass(state);
		that.ispure = that.ispure && state.ispure;
	}
	if (that.last is null) {
		that.last = new TupleLit();
	}
	semantic1(that.last, trace);
	that.type = that.last.type;
}

void semantic1ExpressionImpl(FuncLit that, Trace* trace) {
	semantic1(that.argument, trace);
	checkType(that.argument);

	if (that.explict_return) {
		semantic1(that.explict_return, trace);
		checkType(that.explict_return);
		that.type = createType!FCall(that.explict_return, that.argument);
	}
	semantic1(that.text, trace);

	if (that.explict_return) {
		if (!sameType(that.explict_return, that.text.type)) {
			error("Explict return doesn't match actual return", that.pos);
		}
	}
	//ftype.ispure = text.ispure; todo fix me
	if (!that.explict_return) {
		that.type = createType!FCall(that.text.type, that.argument);
	}
	that.ispure = true;
	auto mod = cast(Module) trace.range.reduce!"b".node;
	mod.exports[that.name] = Symbol(that);
}

void semantic1ExpressionImpl(StringLit that, Trace* trace) {
	that.type = createType!ArrayIndex(createType!Char);
	that.ispure = true;
}

void semantic1ExpressionImpl(ArrayLit that, Trace* trace) {
	foreach (value; that.values) {
		semantic1(value, trace);
	}
	if (that.values.length == 0) {
		error("Array Literals must contain at least one element", that.pos);
	}
	auto current = that.values[0].type;
	foreach (value; that.values[1 .. $]) {
		if (!sameType(current, value.type)) {
			error("All elements of an array literal must be of the same type", that.pos);
		}
	}
	that.type = createType!ArrayIndex(current);
	that.ispure = that.values.map!(a => a.ispure).all;
}

void semantic1ExpressionImpl(ExternJS that, Trace* trace) {
	that.type = createType!ExternType;
	that.ispure = true;
	if (that.name == "") {
		error("Improper extern", that.pos);
	}
}

//check if a value's is equal to another type factering in implict coversions
bool sameTypeValueType(ref Expression value, Expression type) {
	assert(value.isRuntimeValue);
	assert(type.isType);
	return sameType(value.type, type) || implicitConvert(value, type);
}

bool sameTypeValueValue(ref Expression left, ref Expression right) {
	assert(left.isRuntimeValue);
	assert(right.isRuntimeValue);
	return sameType(left.type, right.type) || implicitConvertDual(left, right);
}

//checks if two types are the same
bool sameType(Expression a, Expression b) {
	assert(a.isType);
	assert(b.isType);
	alias Types = AliasSeq!(Metaclass, Char, Int, UInt, Struct, Postfix!"(*)",
			ArrayIndex, FCall, ImportType, ExternType);
	return dispatch!((a, b) => dispatch!((a, b) => sameTypeImpl(b, a), Types)(b, a), Types)(a, b);
}

bool sameTypeImpl(T1, T2)(T1 a, T2 b) {
	static if (!is(T1 == T2) || is(T1 == ImportType) || is(T1 == ExternType)) {
		return false;
	} else {
		alias T = T1;
		static if (is(T == Bool) || is(T == Char) || is(T == Metaclass)) {
			return true;
		} else static if (is(T == UInt) || is(T == Int)) {
			return a.size == b.size;
		} else static if (is(T == Struct)) {
			if (a.values.length != b.values.length) {
				return false;
			}
			foreach (c, t; a.values) {
				if (!sameType(t, b.values[c])) {
					return false;
				}
			}
			return true;
		} else static if (is(T == Postfix!"(*)")) {
			return sameType(a.value, b.value);
		} else static if (is(T == ArrayIndex)) {
			return sameType(a.array, b.array);
		} else static if (is(T == FCall)) {
			return sameType(a.fptr, b.fptr) && sameType(a.arg, b.arg);
		}
	}
}
//modifys value's type
//returns if converted
bool implicitConvert(ref Expression value, Expression type) {
	value = value;
	type = type;
	assert(isRuntimeValue(value));
	assert(isType(type));

	if (cast(IntLit) value && (type.isUInt || type.isInt)) {
		auto result = new Cast();
		result.implicit = true;
		result.wanted = type;
		result.type = type;
		result.value = value;
		result.process = true;
		value = result;
		return true;
	}
	if (auto ext = cast(ExternJS) value) {
		auto result = new Cast();
		result.implicit = true;
		result.wanted = type;
		result.type = type;
		result.value = value;
		result.process = true;
		value = result;
		return true;
	}
	return false;
}

//check if two values can convert implictly into each other
bool implicitConvertDual(ref Expression left, ref Expression right) {
	return implicitConvert(left, right.type) || implicitConvert(right, left.type);
}

bool castable(Expression target, Expression want) {
	target = target;
	want = want;
	if (sameType(target, want)) {
		return true;
	}
	if (sameType(target, createType!Struct())) {
		return true;
	}
	if ((cast(Int) target || cast(UInt) target) && (cast(Int) want || cast(UInt) want)) { //casting between int types
		return true;
	}
	return false;
}
