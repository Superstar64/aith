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
	semantic1(mod, null);
}

Expression unalias(Expression expression) {
	if (auto unknown = cast(Variable) expression) {
		if (unknown.definition.manifest) {
			return unknown.definition.definition;
		}
	}
	return expression;
}

Bool isBool(Expression type) {
	return cast(Bool) type.unalias;
}

Char isChar(Expression type) {
	return cast(Char) type.unalias;
}

Int isInt(Expression type) {
	return cast(Int) type.unalias;
}

UInt isUInt(Expression type) {
	return cast(UInt) type.unalias;
}

Postfix!"(*)" isPointer(Expression type) {
	return cast(Postfix!"(*)") type.unalias;
}

//todo remove these
ArrayIndex isArray(Expression type) {
	if (type.isType && cast(ArrayIndex) type.unalias) {
		return cast(ArrayIndex) type.unalias;
	}
	return null;
}

FCall isFunction(Expression type) {
	if (type.isType && cast(FCall) type.unalias) {
		return cast(FCall) type.unalias;
	}
	return null;
}

bool isType(Expression expression) {
	expression = expression.unalias;
	if (expression.isBool || expression.isChar || expression.isInt
			|| expression.isUInt || expression.isPointer) {
		return true;
	}
	if (auto structlit = cast(StructLit) expression) {
		return structlit.values.map!isType.all;
	}
	if (auto array = cast(ArrayIndex) expression) {
		return array.array.isType && array.index.isType;
	}
	if (auto func = cast(FCall) expression) {
		return func.fptr.isType && func.arg.isType;
	}
	if (auto var = cast(Variable) expression) {
		return var.definition.manifest && var.unalias.isType;
	}
	return !!cast(Metaclass) expression;
}

bool isRuntimeValue(Expression expression) {
	expression = expression.unalias;
	//todo implement actual check for runtime values
	if (auto structlit = cast(StructLit) expression) {
		if (structlit.values.length == 0) {
			return true;
		}
	}
	return !expression.isType;
}

void checkRuntimeValue(Expression expression) {
	if (!isRuntimeValue(expression)) {
		error("Expected runtime value", expression.pos);
	}
}

void checkType(Expression expression) {
	if (!isType(expression)) {
		error("Expected type", expression.pos);
	}
}

void checkIntTypeSize(int size, Position pos) {
	if (size == 0) {
		return;
	}
	uint check = 1;
	while (true) {
		if (check == size) {
			return;
		}
		if (check > size) {
			error("Bad Int Size", pos);
		}
		check *= 2;
	}
}

void semantic1(Node that, Trace* trace) {
	if (that.process) {
		error("Cyclic variable", that.pos);
	}
	that.process = true;
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	dispatch!(semantic1Impl, Metaclass, Bool, Char, Int, UInt, Postfix!"(*)",
			ModuleVar, Module, IntLit, CharLit, BoolLit, StructLit, Variable,
			FuncArgument, If, While, New, NewArray, Cast, Dot, ArrayIndex, FCall,
			Slice, ScopeVar, Scope, FuncLit, StringLit, ArrayLit, ExternJS,
			Binary!"*", Binary!"/", Binary!"%", Binary!"+", Binary!"-",
			Binary!"~", Binary!"==", Binary!"!=", Binary!"<=", Binary!">=",
			Binary!"<", Binary!">", Binary!"&&", Binary!"||", Binary!"=",
			Prefix!"+", Prefix!"-", Prefix!"*", Prefix!"/", Prefix!"&", Prefix!"!")(that, trace);
}

void semantic1Impl(Module that, Trace* trace) {
	with (that) {
		foreach (symbol; symbols) {
			if (!symbol.process) {
				semantic1(symbol, trace);
			}
			if (!symbol.ispure) {
				error("Impure expression in global", symbol.pos);
			}
		}
	}
}

Metaclass metaclass;
static this() {
	metaclass = new Metaclass();
	metaclass.type = metaclass;
	metaclass.ispure = true;
}

void semantic1Impl(Metaclass that, Trace* trace) {

}

void semantic1Impl(T)(T that, Trace* trace) if (is(T == Bool) || is(T == Char)) {
	with (that) {
		that.type = metaclass;
		that.ispure = true;
	}
}

void semantic1Impl(T)(T that, Trace* trace) if (is(T == Int) || is(T == UInt)) {
	with (that) {
		checkIntTypeSize(size, pos);
		that.type = metaclass;
		that.ispure = true;
	}
}

void semantic1Impl(T)(T that, Trace* trace) if (is(T == Postfix!"(*)")) {
	with (that) {
		//todo reorder
		semantic1(value, trace);
		checkType(value);
		type = metaclass;
		that.ispure = true;
	}
}

void semantic1Impl(ModuleVar that, Trace* trace) {
	with (that) {
		semantic1(definition, trace);
		//todo metaclasses
		checkRuntimeValue(definition);
		ispure = definition.ispure;
	}
}

void semantic1Impl(IntLit that, Trace* trace) {
	with (that) {
		if (usigned) {
			type = new UInt(0);
		} else {
			type = new Int(0);
		}
		ispure = true;
	}
}

void semantic1Impl(CharLit that, Trace* trace) {
	with (that) {
		type = new Char();
		ispure = true;
	}
}

void semantic1Impl(BoolLit that, Trace* trace) {
	with (that) {
		type = new Bool();
		ispure = true;
	}
}

void semantic1Impl(StructLit that, Trace* trace) {
	with (that) {
		foreach (value; values) {
			semantic1(value, trace);
		}
		//todo fix me, make untypes structs have no type eg.. (())
		if (that.values.length != 0 && values.map!isType.all) {
			type = metaclass;
		} else {
			auto structType = new StructLit();
			structType.names = names;
			structType.values = values.map!(a => a.type).array;
			type = structType;
			values.each!checkRuntimeValue;
		}
		ispure = values.map!(a => a.ispure).all;
	}
}

//todo remember to put unalias before doing checks on values

void semantic1Impl(Variable that, Trace* trace) {
	with (that) {
		Trace subTrace;
		auto source = trace.search(name, namespace, subTrace);
		if (source is null) {
			error("Unknown variable", pos);
		}
		if (source.type is null) {
			semantic1(source, &subTrace);
		}
		assert(source.type);
		that.definition = source;
		type = source.type;
		lvalue = !source.manifest;
		ispure = source.manifest;

	}
}

void semantic1Impl(FuncArgument that, Trace* trace) {
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

void semantic1Impl(If that, Trace* trace) {
	with (that) {
		semantic1(cond, trace);
		checkRuntimeValue(cond);
		semantic1(yes, trace);
		checkRuntimeValue(yes);
		semantic1(no, trace);
		checkRuntimeValue(no);
		if (!cond.type.isBool) {
			error("Boolean expected in if expression", cond.pos);
		}
		if (!(sameType(yes.type, no.type) || implicitConvertIntDual(yes, no))) {
			error("If expression with the true and false parts having different types", pos);
		}
		type = yes.type;
		ispure = cond.ispure && yes.ispure && no.ispure;
	}
}

void semantic1Impl(While that, Trace* trace) {
	with (that) {
		semantic1(cond, trace);
		checkRuntimeValue(cond);
		semantic1(state, trace);
		checkRuntimeValue(state);
		if (!cond.type.isBool) {
			error("Boolean expected in while expression", cond.pos);
		}
		type = new StructLit();
		ispure = cond.ispure && state.ispure;
	}
}

void semantic1Impl(New that, Trace* trace) {
	with (that) {
		semantic1(value, trace);
		checkRuntimeValue(value);
		auto ptr = new Postfix!"(*)"();
		ptr.value = value.type;
		type = ptr;
		ispure = value.ispure;
	}
}

void semantic1Impl(NewArray that, Trace* trace) {
	with (that) {
		semantic1(length, trace);
		checkRuntimeValue(length);
		semantic1(value, trace);
		checkRuntimeValue(value);
		if (!(sameType(length.type, new UInt(0)) || implicitConvertInt(length, new UInt(0)))) {
			error("Can only create an array with length of UInts", length.pos);
		}
		auto array = new ArrayIndex();
		array.array = value.type;
		array.index = new StructLit();
		type = array;
		ispure = length.ispure && value.ispure;
	}
}

void semantic1Impl(Cast that, Trace* trace) {
	with (that) {
		semantic1(value, trace);
		checkRuntimeValue(value);
		semantic1(wanted, trace);
		checkType(wanted);
		if (!castable(value.type, wanted)) {
			error("Unable to cast", pos);
		}
		type = wanted;
		ispure = value.ispure;
	}
}

void semantic1Impl(Dot that, Trace* trace) {
	with (that) {
		semantic1(value, trace);
		checkRuntimeValue(value);
		semantic1Dot(value.type, trace, that);
		ispure = value.ispure;
	}
}

void semantic1Dot(Expression that, Trace* trace, Dot dot) {
	dispatch!(semantic1DotImpl, StructLit, ArrayIndex, Expression)(that.unalias, trace, dot);
}

void semantic1DotImpl(T)(T that, Trace* trace, Dot dot) {
	if (cycle(that, trace)) {
		return;
	}
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	with (that)
		static if (is(T == StructLit)) {
			auto index = dot.index;
			if (index.peek!string) {
				auto str = index.get!string;
				if (!(str in names)) {
					error("Unable to find field", dot.pos);
				}
				dot.type = values[names[str]];
			} else {
				uint typeIndex = index.get!(BigInt).toInt;
				if (typeIndex >= values.length) {
					error("Index number to high", dot.pos);
				}
				dot.type = values[typeIndex];
			}
			dot.lvalue = dot.value.lvalue;
		} else static if (is(T == ArrayIndex)) {
			auto index = dot.index;
			if (!(index.peek!string && index.get!string == "length")) {
				semantic1DotImpl!Expression(that, trace, dot);
				return;
			}
			dot.type = new UInt(0);
		} else static if (is(T == Expression)) {
			error("Unable to dot", pos);
		} else {
			pragma(msg, T);
			static assert(0);
		}
}

void semantic1Impl(ArrayIndex that, Trace* trace) {
	with (that) {
		semantic1(array, trace);
		semantic1(index, trace);
		if (array.isType) {
			if (!(index.isType && sameType(index, new StructLit()))) {
				error("Expected empty type in array type", pos);
			}
			type = metaclass;
			ispure = true;
		} else {
			if (!array.type.isArray) {
				error("Unable able to index", pos);
			}
			if (!(sameType(index.type, new UInt(0)) || implicitConvertInt(index, new UInt(0)))) {
				error("Can only index an array with UInts", pos);
			}
			auto arrayType = array.type.isArray;
			type = arrayType.array;
			lvalue = true;
			ispure = array.ispure && index.ispure;
		}
	}
}

void semantic1Impl(FCall that, Trace* trace) {
	with (that) {
		semantic1(fptr, trace);
		semantic1(arg, trace);
		if (fptr.isType) {

		} else {
			auto fun = fptr.type.isFunction;
			if (!fun) {
				error("Not a function", pos);
			}
			if (!(sameType(fun.arg, arg.type) || ((fun.arg.isInt
					|| fun.arg.isUInt) && implicitConvertInt(arg, fun.arg)))) {
				error("Unable to call function with the  argument's type", pos);
			}
			type = fun.fptr;
			ispure = fptr.ispure && arg.ispure /* todo fix me && fun.ispure*/ ;
		}
	}
}

void semantic1Impl(Slice that, Trace* trace) {
	with (that) {
		semantic1(array, trace);
		checkRuntimeValue(array);
		semantic1(left, trace);
		checkRuntimeValue(left);
		semantic1(right, trace);
		checkRuntimeValue(right);
		if (!array.type.isArray) {
			error("Not an array", pos);
		}
		if (!(sameType(right.type, new UInt(0)) || implicitConvertInt(left,
				new UInt(0))) || !(sameType(right.type, new UInt(0))
				|| implicitConvertInt(right, new UInt(0)))) {
			error("Can only index an array with UInts", pos);
		}
		type = array.type;
		ispure = array.ispure && left.ispure && right.ispure;
	}
}

void semantic1Impl(string op)(Binary!op that, Trace* trace) {
	with (that) {
		semantic1(left, trace);
		checkRuntimeValue(left);
		semantic1(right, trace);
		checkRuntimeValue(right);
		static if (["*", "/", "%", "+", "-", "<=", ">=", ">", "<"].canFind(op)) {
			auto ty = left.type;
			if (!((ty.isUInt || ty.isInt) && (sameType(ty, right.type)
					|| implicitConvertIntDual(left, right)))) {
				error(op ~ " only works on Ints or UInts of the same Type", pos);
			}
			static if (["<=", ">=", ">", "<"].canFind(op)) {
				type = new Bool();
			} else {
				type = ty;
			}
			ispure = left.ispure && right.ispure;
		} else static if (op == "~") {
			auto ty = left.type;
			if (!ty.isArray && sameType(ty, right.type)) {
				error("~ only works on Arrays of the same Type", pos);
			}
			type = ty;
			ispure = left.ispure && right.ispure;
		} else static if (["==", "!="].canFind(op)) {
			if (!(sameType(left.type, right.type) || implicitConvertIntDual(left, right))) {
				error(op ~ " only works on the same Type", pos);
			}
			type = new Bool();
			ispure = left.ispure && right.ispure;
		} else static if (["&&", "||"].canFind(op)) {
			auto ty = left.type;
			if (!(ty.isBool && sameType(ty, right.type))) {
				error(op ~ " only works on Bools", pos);
			}
			type = new Bool();
			ispure = left.ispure && right.ispure;
		} else static if (op == "=") {
			if (!(sameType(left.type, right.type) || implicitConvertInt(right, left.type))) {
				error("= only works on the same type", pos);
			}
			if (!left.lvalue) {
				error("= only works on lvalues", pos);
			}
			type = left.type;
			ispure = left.ispure && right.ispure;
		} else {
			static assert(0);
		}
	}
}

void semantic1Impl(string op)(Prefix!op that, Trace* trace) {
	with (that) {
		semantic1(value, trace);
		checkRuntimeValue(value);
		static if (op == "-") {
			if (!value.type.isInt) {
				error("= only works Signed Ints", pos);
			}
			type = value.type;
			ispure = value.ispure;
		} else static if (op == "*") {
			if (!value.type.isPointer) {
				error("* only works on pointers", pos);
			}
			type = value.type.isPointer.value;
			lvalue = true;
			ispure = value.ispure;
		} else static if (op == "&") {
			if (!value.lvalue) {
				error("& only works lvalues", pos);
			}

			static void assignHeapImpl(T)(T that, Trace* trace) {
				auto nextTrace = Trace(that, trace);
				trace = &nextTrace;
				static if (is(T == Variable)) {

					that.definition.heap = true;
				} else static if (is(T == Dot)) {
					assignHeap(that.value, trace);
				}
			}

			static void assignHeap(Node that, Trace* trace) {
				return dispatch!(assignHeapImpl, Variable, Dot, Node)(that, trace);
			}

			assignHeap(value, trace);

			auto ptr = new Postfix!"(*)"();
			ptr.value = value.type;
			type = ptr;
			ispure = value.ispure;
		} else static if (op == "!") {
			if (!value.type.isBool) {
				error("! only works on Bools", pos);
			}
			type = value.type;
			ispure = value.ispure;
		} else static if (["+", "/"].canFind(op)) {
			error(op ~ " not supported", pos);
		} else {
			static assert(0);
		}
	}
}

void semantic1Impl(ScopeVar that, Trace* trace) {
	with (that) {
		semantic1(definition, trace);
		checkRuntimeValue(definition);
		ispure = definition.ispure;
	}
}

void semantic1Impl(Scope that, Trace* trace) {
	with (that) {
		ispure = true;
		foreach (type; symbols) {
			semantic1(type, trace);
		}
		foreach (state; states) {
			semantic1(state, trace);
			if (auto expression = cast(Expression) state) {
				checkRuntimeValue(expression);
			}
			trace.context.pass(state);
			ispure = ispure && state.ispure;
		}
		if (last is null) {
			last = new StructLit();
		}
		semantic1(last, trace);
		type = last.type;
	}
}

void semantic1Impl(FuncLit that, Trace* trace) {
	with (that) {
		auto ftype = new FCall();
		semantic1(argument, trace);
		checkType(argument);
		ftype.arg = argument;

		if (explict_return) {
			semantic1(explict_return, trace);
			checkType(explict_return);
			ftype.fptr = explict_return;
			type = ftype;
		}
		semantic1(text, trace);
		checkRuntimeValue(text);
		if (explict_return) {
			if (!sameType(explict_return, text.type)) {
				error("Explict return doesn't match actual return", pos);
			}
		}
		ftype.fptr = text.type;
		//ftype.ispure = text.ispure; todo fix me
		type = ftype;
		ispure = true;
	}
}

void semantic1Impl(StringLit that, Trace* trace) {
	with (that) {
		auto array = new ArrayIndex;
		array.array = new Char;
		array.index = new StructLit();
		type = array;
		ispure = true;
	}
}

void semantic1Impl(ArrayLit that, Trace* trace) {
	with (that) {
		foreach (value; values) {
			semantic1(value, trace);
			checkRuntimeValue(value);
		}
		if (values.length == 0) {
			error("Array Literals must contain at least one element", pos);
		}
		auto current = values[0].type;
		foreach (value; values[1 .. $]) {
			if (!sameType(current, value.type)) {
				error("All elements of an array literal must be of the same type", pos);
			}
		}
		auto array = new ArrayIndex;
		array.array = current;
		array.index = new StructLit();
		type = array;
		ispure = true;
		foreach (value; values) {
			ispure = ispure && value.ispure;
		}
	}
}

void semantic1Impl(ExternJS that, Trace* trace) {
	with (that) {
		semantic1(type, trace);
		checkType(type);
		ispure = true;
	}
}

//modifys value's type
//returns if converted
bool implicitConvertInt(Expression value, Expression type) {
	value = value.unalias;
	type = type.unalias;
	assert(isRuntimeValue(value));
	assert(isType(type));

	if (cast(IntLit) value && (type.isUInt || type.isInt)) {
		value.type = type;
		return true;
	}
	if (cast(StructLit) value && cast(StructLit)(type)) {
		auto str = cast(StructLit) value;
		auto target = cast(StructLit) type;
		foreach (c, ref sub; str.values) {
			if (sameType(sub.type, target.values[c])) {
				continue;
			}
			if (implicitConvertInt(sub, target.values[c])) {
				continue;
			}
			return false;
		}
		return true;
	}
	return false;
}

bool implicitConvertIntDual(Expression left, Expression right) {
	return implicitConvertInt(left, right.type) || implicitConvertInt(right, left.type);
}

bool sameType(Expression a, Expression b) {
	assert(a.isType);
	assert(b.isType);
	alias Types = AliasSeq!(Metaclass, Char, Int, UInt, StructLit,
			Postfix!"(*)", ArrayIndex, FCall);
	return dispatch!((a, b) => dispatch!((a, b) => sameTypeImpl(b, a), Types)(b, a), Types)(
			a.unalias, b.unalias);
}

bool sameTypeImpl(T1, T2)(T1 a, T2 b) {
	static if (!is(T1 == T2)) {
		return false;
	} else {
		alias T = T1;
		static if (is(T == Bool) || is(T == Char) || is(T == Metaclass)) {
			return true;
		} else static if (is(T == UInt) || is(T == Int)) {
			return a.size == b.size;
		} else static if (is(T == StructLit)) {
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

bool castable(Expression target, Expression want) {
	target = target.unalias;
	want = want.unalias;
	if (sameType(target, want)) {
		return true;
	}
	if (sameType(target, new StructLit())) {
		return true;
	}
	if ((cast(Int) target || cast(UInt) target) && (cast(Int) want || cast(UInt) want)) { //casting between int types
		return true;
	}
	return false;
}
