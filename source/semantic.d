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
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	dispatch!(semantic1Impl, Bool, Char, Int, UInt, Struct, Pointer, Array,
			Function, SubType, IndexType, UnknownType, ModuleVar, Module, IntLit, CharLit,
			BoolLit, StructLit, Variable, If, While, New, NewArray, Cast, Dot,
			ArrayIndex, FCall, Slice, ScopeVar, Scope, FuncLitVar, FuncLit, Return,
			StringLit, ArrayLit, ExternJS, Binary!"*", Binary!"/",
			Binary!"%", Binary!"+", Binary!"-", Binary!"~", Binary!"&",
			Binary!"|", Binary!"^", Binary!"<<", Binary!">>", Binary!">>>",
			Binary!"==", Binary!"!=", Binary!"<=", Binary!">=", Binary!"<",
			Binary!">", Binary!"&&", Binary!"||", Binary!"=", Prefix!"+",
			Prefix!"-", Prefix!"*", Prefix!"/", Prefix!"&", Prefix!"~", Prefix!"!")(that, trace);
}

void semantic1Impl(Module that, Trace* trace) {
	with (that) {
		foreach (type; aliases) {
			semantic1(type, trace);
		}
		foreach (var; vars) {
			if (!var.process) {
				semantic1(var, trace);
			}
			if (!var.ispure) {
				error("Impure expression in global", var.pos);
			}
		}
	}
}

void semantic1Impl(T)(T that, Trace* trace) if (is(T == Bool) || is(T == Char)) {

}

void semantic1Impl(T)(T that, Trace* trace) if (is(T == Int) || is(T == UInt)) {
	with (that) {
		checkIntTypeSize(size, pos);
	}
}

void semantic1Impl(Struct that, Trace* trace) {
	with (that) {
		types.each!(a => semantic1(a, trace));
	}
}

void semantic1Impl(T)(T that, Trace* trace) if (is(T == Pointer) || is(T == Array)) {
	with (that) {
		semantic1(type, trace);
	}
}

void semantic1Impl(Function that, Trace* trace) {
	with (that) {
		semantic1(arg, trace);
		semantic1(ret, trace);
	}
}

void semantic1CheckTypeLoop(Type that, Type root) {
	dispatch!(semantic1CheckTypeLoopImpl, Struct, IndirectType, Type)(that, root);
}

void semantic1Impl(SubType that, Trace* trace) {
	with (that) {
		semantic1(type, trace);
		actual_ = semantic1Dereference(type.actual);
		semantic1CheckTypeLoop(actual_, that);
	}
}

Type semantic1Dereference(Type that) {
	return dispatch!(semantic1DereferenceImpl, Pointer, Type)(that);
}

void semantic1CheckTypeLoopImpl(T)(T that, Type root) {
	with (that)
		static if (is(T == Struct)) {
			semantic1CheckTypeLoopImpl!Type(that, root);
			foreach (type; types) {
				semantic1CheckTypeLoop(type, root);
			}
		} else static if (is(T == IndirectType)) {
			semantic1CheckTypeLoopImpl!Type(that, root);
			if (actual_) {
				semantic1CheckTypeLoop(actual_, root);
			}
		} else static if (is(T == Type)) {
			if (that is root) {
				error("Self referecing type", pos);
			}
		} else {
			static assert(0);
		}
}

Type semantic1DereferenceImpl(T)(T that) {
	with (that)
		static if (is(T == Pointer)) {
			return type;
		} else static if (is(T == Type)) {
			error("Unable to deref", pos);
			assert(0);
		} else {
			static assert(0);
		}
}

void semantic1Impl(IndexType that, Trace* trace) {
	with (that) {
		semantic1(type, trace);
		actual_ = semantic1IndexType(type.actual, index);
		semantic1CheckTypeLoop(actual_, that);
	}
}

Type semantic1IndexType(Type that, Index index) {
	return dispatch!(semantic1IndexTypeImpl, Struct, Array, Type)(that, index);
}

Type semantic1IndexTypeImpl(T)(T that, Index index) {
	with (that)
		static if (is(T == Struct)) {
			if (index.peek!BigInt) {
				int where = index.get!BigInt.toInt;
				if (where >= types.length) {
					error("Index to big", pos);
				}
				return types[where];
			} else {
				auto name = index.get!string;
				if (auto where = name in names) {
					return types[*where];
				}
				error("Unknown field", pos);
				assert(0);
			}
		} else static if (is(T == Array)) {
			if (index.peek!string && index.get!string == "length") {
				return new UInt(0);
			}
			return semantic1IndexTypeImpl!Type(that, index);
		} else static if (is(T == Type)) {
			error("Unable to get member:" ~ index.to!string, pos);
			assert(0);
		} else {
			static assert(0);
		}
}

void semantic1Impl(UnknownType that, Trace* trace) {
	with (that) {
		auto searched = trace.searchType(name, namespace);
		if (!searched) {
			error("Unknown identifier", pos);
		}
		actual_ = searched;
		semantic1CheckTypeLoop(actual_, that);
	}
}

void semantic1Impl(ModuleVar that, Trace* trace) {
	with (that) {
		if (process) {
			error("Forward declartion", pos);
		}
		process = true;
		semantic1(def, trace);
		ispure = def.ispure;
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
		auto structType = new Struct();
		structType.names = names;
		structType.types = values.map!(a => a.type).array;
		type = structType;
		ispure = values.map!(a => a.ispure).all;
	}
}

void semantic1Impl(Variable that, Trace* trace) {
	with (that) {
		Trace subTrace;
		auto vardef = trace.searchVar(name, namespace, subTrace);
		if (vardef is null) {
			error("Unable to find variable", pos);
		}
		if (cast(ModuleVar) vardef && (cast(ModuleVar) vardef).getType is null) {
			semantic1(vardef, &subTrace);
		}
		assert(vardef.getType);
		type = vardef.getType;
		lvalue = !vardef.manifest;
		if (cast(ModuleVar) vardef) {
			ispure = false;
		} else {
			ispure = true;
		}
	}
}

void semantic1Impl(If that, Trace* trace) {
	with (that) {
		semantic1(cond, trace);
		semantic1(yes, trace);
		semantic1(no, trace);
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
		semantic1(state, trace);
		if (!cond.type.isBool) {
			error("Boolean expected in while expression", cond.pos);
		}
		type = new Struct();
		ispure = cond.ispure && state.ispure;
	}
}

void semantic1Impl(New that, Trace* trace) {
	with (that) {
		semantic1(value, trace);
		auto ptr = new Pointer();
		ptr.type = value.type;
		type = ptr;
		ispure = value.ispure;
	}
}

void semantic1Impl(NewArray that, Trace* trace) {
	with (that) {
		semantic1(length, trace);
		semantic1(value, trace);
		if (!(sameType(length.type, new UInt(0)) || implicitConvertInt(length, new UInt(0)))) {
			error("Can only create an array with length of UInts", length.pos);
		}
		auto array = new Array();
		array.type = value.type;
		type = array;
		ispure = length.ispure && value.ispure;
	}
}

void semantic1Impl(Cast that, Trace* trace) {
	with (that) {
		semantic1(value, trace);
		semantic1(wanted, trace);
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
		semantic1Dot(value.type, trace, that);
		ispure = value.ispure;
	}
}

void semantic1Dot(Type that, Trace* trace, Dot dot) {
	dispatch!(semantic1DotImpl, Struct, Array, IndirectType, Type)(that, trace, dot);
}

void semantic1DotImpl(T)(T that, Trace* trace, Dot dot) {
	if (cycle(that, trace)) {
		return;
	}
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	with (that)
		static if (is(T == Struct)) {
			auto index = dot.index;
			if (index.peek!string) {
				auto str = index.get!string;
				if (!(str in names)) {
					error("Unable to find field", dot.pos);
				}
				dot.type = types[names[str]];
			} else {
				uint typeIndex = index.get!(BigInt).toInt;
				if (typeIndex >= types.length) {
					error("Index number to high", dot.pos);
				}
				dot.type = types[typeIndex];
			}
			dot.lvalue = dot.value.lvalue;
		} else static if (is(T == Array)) {
			auto index = dot.index;
			if (!(index.peek!string && index.get!string == "length")) {
				semantic1DotImpl!Type(that, trace, dot);
				return;
			}
			dot.type = new UInt(0);
		} else static if (is(T == IndirectType)) {
			semantic1Dot(actual_, trace, dot);
		} else static if (is(T == Type)) {
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
		if (!array.type.isArray) {
			error("Unable able to index", pos);
		}
		if (!(sameType(index.type, new UInt(0)) || implicitConvertInt(index, new UInt(0)))) {
			error("Can only index an array with UInts", pos);
		}
		auto arrayType = array.type.isArray;
		type = arrayType.type;
		lvalue = true;
		ispure = array.ispure && index.ispure;
	}
}

void semantic1Impl(FCall that, Trace* trace) {
	with (that) {
		semantic1(fptr, trace);
		semantic1(arg, trace);
		auto fun = fptr.type.isFunction;
		if (!fun) {
			error("Not a function", pos);
		}
		if (!(sameType(fun.arg, arg.type) || ((fun.arg.isInt
				|| fun.arg.isUInt) && implicitConvertInt(arg, fun.arg)))) {
			error("Unable to call function with arg's type", pos);
		}
		type = fun.ret;
		ispure = fptr.ispure && fun.ispure && arg.ispure;
	}
}

void semantic1Impl(Slice that, Trace* trace) {
	with (that) {
		semantic1(array, trace);
		semantic1(left, trace);
		semantic1(right, trace);
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
		semantic1(right, trace);
		static if (["*", "/", "%", "+", "-", "&", "|", "^", "<<", ">>", ">>>",
				"<=", ">=", ">", "<"].canFind(op)) {
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
			type = value.type.isPointer.type;
			lvalue = true;
			ispure = value.ispure;
		} else static if (op == "~") {
			if (!(value.type.isUInt || value.type.isInt)) {
				error("~ only works on Ints and UInts", pos);
			}
			type = value.type;
			ispure = value.ispure;
		} else static if (op == "&") {
			if (!value.lvalue) {
				error("& only works lvalues", pos);
			}

			static void assignHeapImpl(T)(T that, Trace* trace) {
				auto nextTrace = Trace(that, trace);
				trace = &nextTrace;
				static if (is(T == Variable)) {
					Var var = trace.searchVar(that.name, that.namespace);
					var.heap = true;
				} else static if (is(T == Dot)) {
					assignHeap(that.value, trace);
				}
			}

			static void assignHeap(Node that, Trace* trace) {
				return dispatch!(assignHeapImpl, Variable, Dot, Node)(that, trace);
			}

			assignHeap(value, trace);

			auto ptr = new Pointer();
			ptr.type = value.type;
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
		semantic1(def, trace);
		ispure = def.ispure;
	}
}

void semantic1Impl(Scope that, Trace* trace) {
	with (that) {
		ispure = true;
		foreach (type; aliases) {
			semantic1(type, trace);
		}
		foreach (state; states) {
			semantic1(state, trace);
			trace.context.pass(state);
			ispure = ispure && state.ispure;
		}
		if (type is null) {
			type = new Struct();
		}
		if (!(states.map!(a => returns(a, 0)).any || sameType(type, new Struct()))) {
			error("Missing returns in scope", pos);
		}
	}
}

void semantic1Impl(FuncLitVar that, Trace* trace) {
	with (that) {
		semantic1(ty, trace);
		ispure = true;
	}
}

void semantic1Impl(FuncLit that, Trace* trace) {
	with (that) {
		auto ftype = new Function();
		semantic1(fvar, trace);
		ftype.arg = fvar.ty;

		if (explict_return) {
			semantic1(explict_return, trace);
			ftype.ret = explict_return;
			type = ftype;
		}
		semantic1(text, trace);

		if (explict_return) {
			if (!sameType(explict_return, text.type)) {
				error("Explict return doesn't match actual return", pos);
			}
		}
		ftype.ret = text.type;
		ftype.ispure = text.ispure;
		type = ftype;
		ispure = true;
	}
}

void semantic1Impl(Return that, Trace* trace) {
	with (that) {
		semantic1(value, trace);
		bool max = upper == uint.max;
		auto range = trace.range.filter!(a => a.context);
		if (range.empty || !cast(Scope) range.front.node) {
			error("Must return from a scope", pos);
		}
		Node node;
		if (max) {
			node = range.until!(a => !cast(Scope) a.node).reduce!"b".node;
		} else {
			if (range.save.take(upper).any!(a => !cast(Scope) a.context)) {
				error("Tried to return past function");
			}
			node = range.drop(upper).front.node;
		}
		auto target = cast(Scope) node;
		assert(target);

		if (target.type is null) {
			target.type = value.type;
		} else {
			if (!sameType(target.type, value.type)) {
				error("Doesn't match return type", pos);
			}
		}
		type = value.type;
		ispure = value.ispure;
	}
}

void semantic1Impl(StringLit that, Trace* trace) {
	with (that) {
		auto array = new Array;
		array.type = new Char;
		type = array;
		ispure = true;
	}
}

void semantic1Impl(ArrayLit that, Trace* trace) {
	with (that) {
		foreach (value; values) {
			semantic1(value, trace);
		}
		if (values.length == 0) {
			error("Array Literals must contain at least one element", pos);
		}
		Type current = values[0].type;
		foreach (value; values[1 .. $]) {
			if (!sameType(current, value.type)) {
				error("All elements of an array literal must be of the same type", pos);
			}
		}
		auto array = new Array;
		array.type = current;
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
		ispure = true;
	}
}

bool returns(Statement that, uint level) {
	return dispatch!(returnsImpl, IntLit, CharLit, BoolLit, StructLit, Variable,
			If, While, New, NewArray, Cast, Dot, ArrayIndex, FCall, Slice, ScopeVar,
			Scope, FuncLitVar, FuncLit, Return, StringLit, ArrayLit, ExternJS,
			Binary!"*", Binary!"/", Binary!"%", Binary!"+", Binary!"-",
			Binary!"~", Binary!"&", Binary!"|", Binary!"^", Binary!"<<",
			Binary!">>", Binary!">>>", Binary!"==", Binary!"!=", Binary!"<=",
			Binary!">=", Binary!"<", Binary!">", Binary!"&&", Binary!"||",
			Binary!"=", Prefix!"+", Prefix!"-", Prefix!"*", Prefix!"/",
			Prefix!"&", Prefix!"~", Prefix!"!")(that, level);
}

bool returnsImpl(T)(T that, uint level) {
	with (that)
		static if (is(T == IntLit)) {
			return false;
		} else static if (is(T == CharLit)) {
			return false;
		} else static if (is(T == BoolLit)) {
			return false;
		} else static if (is(T == StructLit)) {
			return values.map!(a => a.returns(level)).any;
		} else static if (is(T == Variable)) {
			return false;
		} else static if (is(T == If)) {
			return cond.returns(level) || (yes.returns(level) && no.returns(level));
		} else static if (is(T == While)) {
			return cond.returns(level);
		} else static if (is(T == New)) {
			return value.returns(level);
		} else static if (is(T == NewArray)) {
			return length.returns(level) || value.returns(level);
		} else static if (is(T == Cast)) {
			return value.returns(level);
		} else static if (is(T == Dot)) {
			return value.returns(level);
		} else static if (is(T == ArrayIndex)) {
			return array.returns(level) || index.returns(level);
		} else static if (is(T == FCall)) {
			return fptr.returns(level) || arg.returns(level);
		} else static if (is(T == Slice)) {
			return array.returns(level) || left.returns(level) || right.returns(level);
		} else static if (is(T == Binary!op, string op)) {
			return left.returns(level) || right.returns(level);
		} else static if (is(T == Prefix!op, string op)) {
			return value.returns(level);
		} else static if (is(T == ScopeVar)) {
			return def.returns(level);
		} else static if (is(T == Scope)) {
			return states.map!(a => a.returns(level + 1)).any;
		} else static if (is(T == FuncLitVar)) {
			return false;
		} else static if (is(T == FuncLit)) {
			return false;
		} else static if (is(T == Return)) {
			return value.returns(level) || level == upper;
		} else static if (is(T == StringLit)) {
			return false;
		} else static if (is(T == ArrayLit)) {
			return values.map!(a => a.returns(level)).any;
		} else static if (is(T == ExternJS)) {
			return false;
		} else {
			static assert(0);
		}
}

//modifys value's type
//returns if converted
bool implicitConvertInt(Value value, Type type) {
	if (cast(IntLit) value && (type.isUInt || type.isInt)) {
		value.type = type;
		return true;
	}
	if (cast(StructLit) value && cast(Struct)(type)) {
		auto str = cast(StructLit) value;
		auto target = cast(Struct) type;
		foreach (c, ref sub; str.values) {
			if (sameType(sub.type, target.types[c])) {
				continue;
			}
			if (implicitConvertInt(sub, target.types[c])) {
				continue;
			}
			return false;
		}
		return true;
	}
	return false;
}

bool implicitConvertIntDual(Value left, Value right) {
	return implicitConvertInt(left, right.type) || implicitConvertInt(right, left.type);
}

bool sameType(Type a, Type b) {
	alias Types = AliasSeq!(Char, Int, UInt, Struct, Pointer, Array, Function);
	return dispatch!((a, b) => dispatch!((a, b) => sameTypeImpl(b, a), Types)(b, a), Types)(
			a.actual, b.actual);
}

bool sameTypeImpl(T1, T2)(T1 a, T2 b) {
	static if (!is(T1 == T2)) {
		return false;
	} else {
		alias T = T1;
		static if (is(T == Bool) || is(T == Char)) {
			return true;
		} else static if (is(T == UInt) || is(T == Int)) {
			return a.size == b.size;
		} else static if (is(T == Struct)) {
			if (a.types.length != b.types.length) {
				return false;
			}
			foreach (c, t; a.types) {
				if (!sameType(t, b.types[c])) {
					return false;
				}
			}
			return true;
		} else static if (is(T == Pointer) || is(T == Array)) {
			return sameType(a.type, b.type);
		} else static if (is(T == Function)) {
			return sameType(a.ret, b.ret) && sameType(a.arg, b.arg);
		}
	}
}

bool castable(Type tar, Type want) {
	tar = tar.actual;
	want = want.actual;
	if (sameType(tar, want)) {
		return true;
	}
	if (sameType(tar, new Struct())) {
		return true;
	}
	if ((cast(Int) tar || cast(UInt) tar) && (cast(Int) want || cast(UInt) want)) { //casting between int types
		return true;
	}
	return false;
}
