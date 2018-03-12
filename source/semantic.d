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
import std.range : recurrence, drop, take;

import ast;
import error : error, Position;

T castTo(T, Base)(Base node) {
	return cast(T) node;
}

void processModule(Module mod) {
	mod.process = true;
	auto trace = Trace(mod, null);
	foreach (symbol; mod.symbols) {
		semantic1(symbol, &trace);
		if (!symbol.ispure) {
			error("Impure expression in global", symbol.position);
		}
	}
}

bool isRuntimeValue(Expression expression) {
	return !(expression.castTo!Type || expression.castTo!Import);
}

void checkRuntimeValue(Expression expression) {
	if (!isRuntimeValue(expression)) {
		error("Expected runtime value", expression.position);
	}
}

Type tryType(ref Replaceable!Expression expression) {
	if (auto tuple = expression.castTo!TupleLit) {
		expression._original ~= expression._value;
		auto structWrap = createType!TypeStruct(tuple.values.map!checkType.array);
		expression._value = structWrap;
		return structWrap;
	}
	if (!expression.castTo!Type) {
		return null;
	}
	return expression.castTo!Type;
}

//makes sure expression is a type or implicitly convert it to a type
Type checkType(ref Replaceable!Expression expression) {
	auto type = tryType(expression);
	if (type is null) {
		error("Expected type", expression.position);
		assert(0);
	}
	return type;
}

Type createType(T, Args...)(Args args) {
	auto type = createTypeImpl!T(args);
	type.process = true;
	return type;
}

T createTypeImpl(T)()
		if (is(T == TypeBool) || is(T == TypeChar) || is(T == TypeImport) || is(T == TypeExtern)) {
	return new T;
}

T createTypeImpl(T)(int size) if (is(T == TypeInt) || is(T == TypeUInt)) {
	auto type = new T;
	type.size = size;
	return type;
}

T createTypeImpl(T)(Type value) if (is(T == TypePointer)) {
	auto type = new T;
	type.value = value;
	return type;
}

T createTypeImpl(T)(Type[] values = null) if (is(T == TypeStruct)) {
	auto type = new T;
	type.values = values;
	return type;
}

T createTypeImpl(T)(Type fptr, Type arg) if (is(T == TypeFunction)) {
	auto type = new T;
	type.fptr = fptr;
	type.arg = arg;
	return type;
}

T createTypeImpl(T)(Type array) if (is(T == TypeArray)) {
	auto type = new T;
	type.array = array;
	return type;
}

void semantic1(Replaceable!Statement that, Trace* trace) {
	if (that.castTo!Expression) {
		semantic1(*cast(Replaceable!Expression*)&that, trace);
		return;
	}
	dispatch!(semantic1, VarDef, Assign)(that, trace);
}

Module upperModule(Trace* trace) {
	return trace.range.reduce!"b".node.castTo!Module;
}

FuncLit upperFunc(Trace* trace) {
	auto range = trace.range.map!(a => a.node).map!(a => a.castTo!FuncLit).filter!(a => !!a);
	if (!range.empty) {
		return range.front;
	}
	return null;
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
		auto explicit = checkType(that.explicitType);
		if (!sameTypeValueType(that.definition, explicit)) {
			error("types don't match", that.position);
		}
	}
	if (!that.manifest) {
		if (auto scopeVar = that.castTo!ScopeVarDef) {
			scopeVar.func = trace.upperFunc;
		}
		if (auto moduleVar = that.castTo!ModuleVarDef) {
			auto mod = trace.upperModule;
			mod.exports[that.name] = Symbol(moduleVar);
		}
	}
}

void semantic1(Assign that, Trace* trace) {
	semantic1(that.left, trace);
	semantic1(that.right, trace);
	if (!(sameType(that.left.type, that.right.type) || implicitConvert(that.right, that.left.type))) {
		error("= only works on the same type", that.position);
	}
	if (!that.left.lvalue) {
		error("= only works on lvalues", that.position);
	}
	that.ispure = that.left.ispure && that.right.ispure;
}

void semantic1(ref Replaceable!Expression that, Trace* trace) {
	if (that.process) {
		//todo check for cycles
		return;
	}
	that.process = true;
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	auto current = that._value;
	dispatch!(semantic1ExpressionImpl, TypeMetaclass, TypeBool, TypeChar, TypeInt, TypeUInt, Import,
			IntLit, CharLit, BoolLit, TupleLit, FuncArgument, If, While, New, NewArray,
			Cast, Slice, Scope, FuncLit, StringLit, ArrayLit, ExternJs,
			Binary!"*", Binary!"/", Binary!"%", Binary!"+", Binary!"-",
			Binary!"~", Binary!"==", Binary!"!=", Binary!"<=", Binary!">=",
			Binary!"<", Binary!">", Binary!"&&", Binary!"||", Prefix!"+",
			Prefix!"-", Prefix!"*", Prefix!"/", Prefix!"&", Prefix!"!", Expression)(
			that._value, trace);
	if (that._value != current) {
		that._original ~= current;
	}
	assert(that.type);
	assert(that.type.castTo!Type);
	assert(!cast(Variable) that);
}
//for types that cases that requre ast modification
void semantic1ExpressionImpl(ref Expression that, Trace* trace) {
	dispatch!(semantic1ExpressionImplWritable, Variable, Dot,
			TypeTemporaryStruct, Index, Call, Postfix!"(*)")(that, trace, that);
}

void semantic1ExpressionImplWritable(Variable that, Trace* trace, ref Expression output) {
	Trace* subTrace;
	auto source = trace.search(that.name, subTrace);
	if (source is null) {
		error("Unknown variable", that.position);
	}

	if (source.definition.type is null) {
		semantic1(source, subTrace);
	}
	Expression thealias;
	if (source.manifest) {
		thealias = source.definition;
	} else {
		if (auto scopeDef = source.castTo!ScopeVarDef) {
			auto scopeRef = new ScopeVarRef();
			scopeRef.definition = scopeDef;
			scopeRef.ispure = true;
			scopeRef.type = source.type;
			scopeRef.lvalue = true;
			thealias = scopeRef;
		} else if (auto moduleDef = source.castTo!ModuleVarDef) {
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
	if (auto scopeVarRef = thealias.castTo!ScopeVarRef) {
		checkNotClosure(scopeVarRef, trace, that.position);
	}
	output = thealias;
}

void semantic1ExpressionImplWritable(TypeTemporaryStruct that, Trace* trace, ref Expression output) {
	semantic1(that.value, trace);
	if (!that.value.castTo!TupleLit) {
		error("expected tuple lit after struct", that.position);
	}
	auto tuple = that.value.castTo!TupleLit;
	auto result = createType!TypeStruct(tuple.values.map!checkType.array);
	output = result;
}

void checkNotClosure(ScopeVarRef that, Trace* trace, Position pos) {
	if (trace.upperFunc !is that.definition.func) {
		error("Closures not supported", pos);
	}
}

void semantic1ExpressionImplWritable(Dot that, Trace* trace, ref Expression output) {
	semantic1(that.value, trace);
	semantic1Dot(that.value.type, trace, that, output);
	that.ispure = that.value.ispure;
}

void semantic1Dot(Expression that, Trace* trace, Dot dot, ref Expression output) {
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	dispatch!(semantic1DotImpl, TypeArray, TypeImport, Type)(that, trace, dot, output);
}

void semantic1DotImpl(TypeArray that, Trace* trace, Dot dot, ref Expression output) {
	if (dot.index != "length") {
		semantic1DotImpl(that.castTo!Type, trace, dot, output);
		return;
	}
	dot.type = createType!TypeUInt(0);
}

void semantic1DotImpl(TypeImport that, Trace* trace, Dot dot, ref Expression output) {
	auto imp = dot.value.castTo!Import;
	if (dot.index !in imp.mod.symbols) {
		error(dot.index ~ " doesn't exist in module", dot.position);
	}
	auto definition = imp.mod.symbols[dot.index];
	if (!definition.visible) {
		error(dot.index ~ " is not visible", dot.position);
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
}

void semantic1DotImpl(Type that, Trace* trace, Dot dot, ref Expression output) {
	error("Unable to dot", that.position);
}

void semantic1ExpressionImpl(TypeMetaclass that, Trace* trace) {
}

void semantic1ExpressionImpl(Import that, Trace* trace) {
	that.type = createType!TypeImport;
	that.ispure = true;
}

void semantic1ExpressionImpl(T)(T that, Trace* trace)
		if (is(T == TypeBool) || is(T == TypeChar)) {
}

void semantic1ExpressionImpl(T)(T that, Trace* trace)
		if (is(T == TypeInt) || is(T == TypeUInt)) {
	if (that.size == 0) {
		return;
	}
	if (!recurrence!((a, n) => a[n - 1] / 2)(that.size).until(1).map!(a => a % 2 == 0).all) {
		error("Bad TypeInt Size", that.position);
	}
}

void semantic1ExpressionImplWritable(Postfix!"(*)" that, Trace* trace, ref Expression output) {
	semantic1(that.value, trace);
	output = createType!TypePointer(that.value.checkType);
}

void semantic1ExpressionImpl(IntLit that, Trace* trace) {
	if (that.usigned) {
		that.type = createType!TypeUInt(0);
	} else {
		that.type = createType!TypeInt(0);
	}
	that.ispure = true;
}

void semantic1ExpressionImpl(CharLit that, Trace* trace) {
	that.type = createType!TypeChar;
	that.ispure = true;
}

void semantic1ExpressionImpl(BoolLit that, Trace* trace) {
	that.type = createType!TypeBool;
	that.ispure = true;
}

void semantic1ExpressionImpl(TupleLit that, Trace* trace) {
	foreach (value; that.values) {
		semantic1(value, trace);
	}
	that.type = createType!TypeStruct(that.values.map!(a => a.type).array);
	that.ispure = that.values.map!(a => a.ispure).all;
}

void semantic1ExpressionImpl(FuncArgument that, Trace* trace) {
	that.type = trace.upperFunc.argument.castTo!Type;
	if (that.type is null) {
		error("$@ without function", that.position);
	}
}

void semantic1ExpressionImpl(If that, Trace* trace) {
	semantic1(that.cond, trace);
	semantic1(that.yes, trace);
	semantic1(that.no, trace);
	if (!that.cond.type.castTo!TypeBool) {
		error("Boolean expected in if expression", that.cond.position);
	}
	if (!sameTypeValueValue(that.yes, that.no)) {
		error("If expression with the true and false parts having different types", that.position);
	}
	that.type = that.yes.type;
	that.ispure = that.cond.ispure && that.yes.ispure && that.no.ispure;
}

void semantic1ExpressionImpl(While that, Trace* trace) {
	semantic1(that.cond, trace);
	semantic1(that.state, trace);
	if (!that.cond.type.castTo!TypeBool) {
		error("Boolean expected in while expression", that.cond.position);
	}
	that.type = createType!TypeStruct();
	that.ispure = that.cond.ispure && that.state.ispure;
}

void semantic1ExpressionImpl(New that, Trace* trace) {
	semantic1(that.value, trace);
	that.type = createType!(TypePointer)(that.value.type);
	that.ispure = that.value.ispure;
}

void semantic1ExpressionImpl(NewArray that, Trace* trace) {
	semantic1(that.length, trace);
	semantic1(that.value, trace);
	if (!sameTypeValueType(that.length, createType!TypeUInt(0))) {
		error("Can only create an array with length of UInts", that.length.position);
	}
	that.type = createType!TypeArray(that.value.type);
	that.ispure = that.length.ispure && that.value.ispure;
}

void semantic1ExpressionImpl(Cast that, Trace* trace) {
	semantic1(that.value, trace);
	semantic1(that.wanted, trace);
	auto wanted = checkType(that.wanted);
	if (!castable(that.value.type, wanted)) {
		error("Unable to cast", that.position);
	}
	that.type = wanted;
	that.ispure = that.value.ispure;
}

bool castable(Type target, Type want) {
	target = target;
	want = want;
	if (sameType(target, want)) {
		return true;
	}
	if (sameType(target, createType!TypeStruct())) {
		return true;
	}
	if ((target.castTo!TypeInt || target.castTo!TypeUInt)
			&& (want.castTo!TypeInt || want.castTo!TypeUInt)) { //casting between int types
		return true;
	}
	return false;
}

void semantic1ExpressionImplWritable(Index that, Trace* trace, ref Expression output) {
	semantic1(that.array, trace);
	semantic1(that.index, trace);
	if (auto array = that.array.castTo!Type) {
		auto index = checkType(that.index);
		if (!sameType(index, createType!TypeStruct())) {
			error("Expected empty type in array type", that.position);
		}
		output = createType!TypeArray(array);
	} else {
		dispatch!(semantic1IndexImpl, TypeArray, TypeStruct, Type)(that.array.type, that, trace);
	}
}

void semantic1IndexImpl(TypeArray type, Index that, Trace* trace) {
	if (!sameTypeValueType(that.index, createType!TypeUInt(0))) {
		error("Can only index an array with UInts", that.position);
	}
	that.type = type.array;
	that.lvalue = true;
	that.ispure = that.array.ispure && that.index.ispure;
}

void semantic1IndexImpl(TypeStruct type, Index that, Trace* trace) {
	auto indexLit = that.index.castTo!IntLit;
	if (!indexLit) {
		error("Expected integer when indexing struct", that.index.position);
	}
	uint index = indexLit.value.to!uint;
	if (index >= type.values.length) {
		error("Index number to high", that.position);
	}
	that.type = type.values[index];
	that.lvalue = that.array.lvalue;
}

void semantic1IndexImpl(Type type, Index that, Trace* trace) {
	error("Unable able to index", that.position);
}

void semantic1ExpressionImplWritable(Call that, Trace* trace, ref Expression output) {
	semantic1(that.fptr, trace);
	semantic1(that.arg, trace);
	if (that.fptr.tryType) {
		auto fptr = checkType(that.fptr);
		auto arg = checkType(that.arg);
		output = createType!TypeFunction(fptr, arg);
	} else {
		auto fun = that.fptr.type.castTo!TypeFunction;
		if (!fun) {
			error("Not a function", that.position);
		}
		if (!sameTypeValueType(that.arg, fun.arg)) {
			error("Unable to call function with the  argument's type", that.position);
		}
		that.type = fun.fptr;
		that.ispure = that.fptr.ispure && that.arg.ispure /* todo fix me && fun.ispure*/ ;
	}
}

void semantic1ExpressionImpl(Slice that, Trace* trace) {
	semantic1(that.array, trace);
	semantic1(that.left, trace);
	semantic1(that.right, trace);
	if (!that.array.type.castTo!TypeArray) {
		error("Not an array", that.position);
	}
	if (!(sameTypeValueType(that.right, createType!TypeUInt(0))
			&& sameTypeValueType(that.left, createType!TypeUInt(0)))) {
		error("Can only index an array with UInts", that.position);
	}
	that.type = that.array.type;
	that.ispure = that.array.ispure && that.left.ispure && that.right.ispure;
}

void semantic1ExpressionImpl(string op)(Binary!op that, Trace* trace) {
	semantic1(that.left, trace);
	semantic1(that.right, trace);
	static if (["*", "/", "%", "+", "-", "<=", ">=", ">", "<"].canFind(op)) {
		auto ty = that.left.type;
		if (!((ty.castTo!TypeUInt || ty.castTo!TypeInt)
				&& (sameTypeValueValue(that.left, that.right)))) {
			error(op ~ " only works on Ints or UInts of the same Type", that.position);
		}
		static if (["<=", ">=", ">", "<"].canFind(op)) {
			that.type = createType!TypeBool;
		} else {
			that.type = ty;
		}
		that.ispure = that.left.ispure && that.right.ispure;
	} else static if (op == "~") {
		auto ty = that.left.type;
		if (!ty.castTo!TypeArray && sameType(ty, that.right.type)) {
			error("~ only works on Arrays of the same Type", that.position);
		}
		that.type = ty;
		that.ispure = that.left.ispure && that.right.ispure;
	} else static if (["==", "!="].canFind(op)) {
		if (!(sameTypeValueValue(that.left, that.right))) {
			error(op ~ " only works on the same Type", that.position);
		}
		that.type = createType!TypeBool;
		that.ispure = that.left.ispure && that.right.ispure;
	} else static if (["&&", "||"].canFind(op)) {
		auto ty = that.left.type;
		if (!(ty.castTo!TypeBool && sameType(ty, that.right.type))) {
			error(op ~ " only works on Bools", that.position);
		}
		that.type = createType!TypeBool;
		that.ispure = that.left.ispure && that.right.ispure;
	} else {
		static assert(0);
	}
}

void semantic1ExpressionImpl(string op)(Prefix!op that, Trace* trace) {
	semantic1(that.value, trace);
	static if (op == "-") {
		if (!that.value.type.castTo!TypeInt) {
			error("= only works Signed Ints", that.position);
		}
		that.type = that.value.type;
		that.ispure = that.value.ispure;
	} else static if (op == "*") {
		if (!that.value.type.castTo!(TypePointer)) {
			error("* only works on pointers", that.position);
		}
		that.type = that.value.type.castTo!(TypePointer).value;
		that.lvalue = true;
		that.ispure = that.value.ispure;
	} else static if (op == "&") {
		if (!that.value.lvalue) {
			error("& only works lvalues", that.position);
		}
		that.type = createType!(TypePointer)(that.value.type);
		that.ispure = that.value.ispure;
	} else static if (op == "!") {
		if (!that.value.type.castTo!TypeBool) {
			error("! only works on Bools", that.position);
		}
		that.type = that.value.type;
		that.ispure = that.value.ispure;
	} else static if (["+", "/"].canFind(op)) {
		error(op ~ " not supported", that.position);
	} else {
		static assert(0);
	}
}

void semantic1ExpressionImpl(Scope that, Trace* trace) {
	that.ispure = true;
	foreach (state; that.children(trace)) {
		semantic1(state, trace);
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
	auto argument = checkType(that.argument);

	if (that.explicit_return) {
		semantic1(that.explicit_return, trace);
		auto explicit_return = checkType(that.explicit_return);
		that.type = createType!TypeFunction(explicit_return, argument);
	}
	semantic1(that.text, trace);

	if (that.explicit_return) {
		auto explicit_return = that.explicit_return.castTo!Type;
		if (!sameType(explicit_return, that.text.type)) {
			error("Explict return doesn't match actual return", that.position);
		}
	} else {
		//todo add purity to function types
		that.type = createType!TypeFunction(that.text.type, argument);
	}
	that.ispure = true;
	auto mod = trace.upperModule;
	mod.exports[that.name] = Symbol(that);
}

void semantic1ExpressionImpl(StringLit that, Trace* trace) {
	that.type = createType!TypeArray(createType!TypeChar);
	that.ispure = true;
}

void semantic1ExpressionImpl(ArrayLit that, Trace* trace) {
	foreach (value; that.values) {
		semantic1(value, trace);
	}
	if (that.values.length == 0) {
		error("Array Literals must contain at least one element", that.position);
	}
	auto head = that.values[0].type;
	foreach (value; that.values[1 .. $]) {
		if (!sameTypeValueType(value, head)) {
			error("All elements of an array literal must be of the same type", that.position);
		}
	}
	that.type = createType!TypeArray(head);
	that.ispure = that.values.map!(a => a.ispure).all;
}

void semantic1ExpressionImpl(ExternJs that, Trace* trace) {
	that.type = createType!TypeExtern;
	that.ispure = true;
	if (that.name == "") {
		error("Improper extern", that.position);
	}
}

//check if a value's is equal to another type factering in implict coversions
bool sameTypeValueType(ref Replaceable!Expression value, Type type) {
	return sameType(value.type, type) || implicitConvert(value, type);
}

bool sameTypeValueValue(ref Replaceable!Expression left, ref Replaceable!Expression right) {
	return sameType(left.type, right.type) || implicitConvertDual(left, right);
}

//checks if two types are the same
bool sameType(Type a, Type b) {
	alias Types = AliasSeq!(TypeMetaclass, TypeBool, TypeChar, TypeInt, TypeUInt,
			TypeStruct, TypePointer, TypeArray, TypeFunction, TypeImport, TypeExtern);
	return dispatch!((a, b) => dispatch!((a, b) => sameTypeImpl(b, a), Types)(b, a), Types)(a, b);
}

bool sameTypeImpl(T1, T2)(T1 a, T2 b) {
	static if (!is(T1 == T2) || is(T1 == TypeImport) || is(T1 == TypeExtern)) {
		return false;
	} else {
		alias T = T1;
		static if (is(T == TypeBool) || is(T == TypeChar) || is(T == TypeMetaclass)) {
			return true;
		} else static if (is(T == TypeUInt) || is(T == TypeInt)) {
			return a.size == b.size;
		} else static if (is(T == TypeStruct)) {
			if (a.values.length != b.values.length) {
				return false;
			}
			foreach (c, t; a.values) {
				if (!sameType(t, b.values[c])) {
					return false;
				}
			}
			return true;
		} else static if (is(T == TypePointer)) {
			return sameType(a.value, b.value);
		} else static if (is(T == TypeArray)) {
			return sameType(a.array, b.array);
		} else static if (is(T == TypeFunction)) {
			return sameType(a.fptr, b.fptr) && sameType(a.arg, b.arg);
		}
	}
}
//modifys value's type
//returns if converted
bool implicitConvert(ref Replaceable!Expression value, Type type) {
	if (value.castTo!IntLit && (type.castTo!TypeUInt || type.castTo!TypeInt)) {
		auto result = new Cast();
		result.implicit = true;
		result.wanted = type;
		result.type = type;
		result.value = value;
		result.process = true;
		result.ispure = value.ispure;
		value._original ~= value._value;
		value._value = result;
		return true;
	}
	if (auto ext = value.castTo!ExternJs) {
		auto result = new Cast();
		result.implicit = true;
		result.wanted = type;
		result.type = type;
		result.value = value;
		result.process = true;
		result.ispure = value.ispure;
		value._original ~= value._value;
		value = result;
		return true;
	}
	return false;
}

//check if two values can convert implictly into each other
bool implicitConvertDual(ref Replaceable!Expression left, ref Replaceable!Expression right) {
	return implicitConvert(left, right.type) || implicitConvert(right, left.type);
}
