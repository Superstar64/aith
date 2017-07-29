/+
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
module codegen;

import std.algorithm : canFind, filter, map;
import std.array : join;
import std.bigint : BigInt;
import std.conv : to;
import std.meta : AliasSeq;
import std.range : chain, drop, enumerate, only;
import std.stdio : write;
import std.string : front, popFront;
import std.typecons : Tuple, tuple;
import std.utf : encode;

import ast;
import error : error;
import semantic;
import jsast;

//structs are repesented as native arrays
//arrays are either a native array or an object with a data, start, length, 
//pointers are arrays
//functions are native js functions

JsState[] generateJSModule(Module mod) {
	JsState[] result;
	auto modTrace = Trace(mod, null);
	foreach (symbol; mod.symbols) {
		uint uuid;
		if (isRuntimeValue(symbol.definition)) {
			result ~= new JsVarDef(symbol.name, generateJS(symbol.definition,
					&modTrace, Usage.once, result, uuid));
		}
	}
	return result;
}

string genName(ref uint uuid) {
	auto vname = "$" ~ uuid.to!string;
	uuid++;
	return vname;
}

JsExpr indexTuple(JsExpr str, size_t index) {
	return new JsIndex(str, new JsLit(index.to!string));
}

JsExpr internalArray(JsExpr array) {
	return new JsBinary!"||"(new JsDot(array, "data"), array);
}

JsExpr arrayStart(JsExpr array) {
	return new JsBinary!"||"(new JsDot(array, "start"), new JsLit("0"));
}

JsExpr arrayLength(JsExpr array) {
	return new JsDot(array, "length");
}

JsExpr indexArray(JsExpr array, JsExpr index) {
	return new JsIndex(internalArray(array), new JsBinary!"+"(arrayStart(array), index));
}

JsExpr indexPointer(JsExpr pointer) {
	return new JsIndex(internalArray(pointer),
			new JsBinary!"||"(new JsDot(pointer, "start"), new JsLit("0")));
}

JsExpr copy(JsExpr expr, Expression type) {
	return dispatch!(copyImpl, Bool, Char, Int, UInt, Postfix!"(*)", ArrayIndex, FCall, Struct)(
			type.unalias, expr);
}

JsExpr copyImpl(T)(T that, JsExpr expr) {
	static if (is(T == Bool) || is(T == Char) || is(T == Int) || is(T == UInt)
			|| is(T == Postfix!"(*)") || is(T == ArrayIndex) || is(T == FCall)) {
		return expr;
	} else static if (is(T == Struct)) {
		auto ret = new JsArray();
		foreach (c, subType; that.values) {
			ret.exprs ~= copy(indexTuple(expr, c), subType);
		}
		return ret;
	} else {
		static assert(0);
	}
}

JsExpr onceCopy(JsExpr expr, Expression type, JsState[] depend, ref uint uuid) {
	return dispatch!(onceCopyImpl, Bool, Char, Int, UInt, Postfix!"(*)",
			ArrayIndex, FCall, Struct)(type.unalias, expr, depend, uuid);
}

JsExpr onceCopyImpl(T)(T that, JsExpr expr, JsState[] depend, ref uint uuid) {
	static if (is(T == Bool) || is(T == Char) || is(T == Int) || is(T == UInt)
			|| is(T == Postfix!"(*)") || is(T == ArrayIndex) || is(T == FCall)) {
		return expr;
	} else static if (is(T == Struct)) {
		auto ret = genTmp(null, expr, depend, uuid);
		return copy(ret, that);
	} else {
		static assert(0);
	}
}

JsExpr defaultValue(Expression type) {
	return dispatch!(defaultValueImpl, Bool, Char, Int, UInt, Postfix!"(*)",
			ArrayIndex, FCall, Struct)(type.unalias);
}

JsExpr defaultValueImpl(T)(T that) {
	static if (is(T == Bool)) {
		return new JsLit("false");
	} else static if (is(T == UInt) || is(T == Int)) {
		return new JsLit("0");
	} else static if (is(T == Char)) {
		return new JsLit('"' ~ "\\0" ~ '"');
	} else static if (is(T == Struct)) {
		auto ret = new JsArray();
		foreach (subType; that.values) {
			ret.exprs ~= defaultValue(subType);
		}
		return ret;
	} else static if (is(T == Postfix!"(*)") || is(T == FCall)) {
		return new JsLit("undefined");
	} else static if (is(T == ArrayIndex)) {
		return new JsArray();
	} else {
		static assert(0);
	}
}

JsExpr castInt(JsExpr expr, Expression type) {
	type = type.unalias;
	if (auto i = cast(Int) type) {
		if (i.size == 1) {
			error("todo support size" ~ i.size.to!string);
			assert(0);
		} else if (i.size == 2) {
			error("todo support size" ~ i.size.to!string);
			assert(0);
		} else if (i.size == 4 || i.size == 0) {
			return new JsBinary!"|"(expr, new JsLit("0"));
		} else {
			error("todo support size" ~ i.size.to!string);
			assert(0);
		}
	} else if (auto i = cast(UInt) type) {
		if (i.size == 1) {
			return new JsBinary!"&"(expr, new JsLit("0xff"));
		} else if (i.size == 2) {
			return new JsBinary!"&"(expr, new JsLit("0xffff"));
		} else if (i.size == 4 || i.size == 0) {
			return new JsBinary!"&"(expr, new JsLit("0xffffffff"));
		} else {
			error("todo support size" ~ i.size.to!string);
			assert(0);
		}
	} else {
		assert(0);
	}
}

JsExpr compare(JsExpr left, JsExpr right, Expression type, JsState[] depend, ref uint uuid) {
	return dispatch!(compareImpl, Bool, Char, Int, UInt, FCall,
			Postfix!"(*)", ArrayIndex, Struct)(type.unalias, left, right, depend, uuid);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, JsState[] depend, ref uint uuid) {
	static if (is(T == Bool) || is(T == Char) || is(T == Int) || is(T == UInt) || is(T == FCall)) {
		return new JsBinary!"=="(left, right);
	} else static if (is(T == Postfix!"(*)")) {
		return new JsBinary!"&&"(new JsBinary!"=="(internalArray(left),
				internalArray(right)), new JsBinary!"=="(arrayStart(left), arrayStart(right)));
	} else static if (is(T == ArrayIndex)) {
		auto var = genName(uuid);
		auto varLit = new JsLit(var);
		depend ~= new JsVarDef(var, new JsBinary!"=="(arrayLength(left), arrayLength(right)));
		auto i = new JsLit(genName(uuid));
		auto loop = new JsFor(new JsVarDef(i.value, new JsLit("0")),
				new JsBinary!"<"(i, arrayLength(left)), new JsPostfix!"++"(i), []);
		depend ~= new JsIf(varLit, [loop], null);
		loop.states ~= new JsBinary!"="(varLit, new JsBinary!"&&"(varLit,
				compare(indexArray(left, i), indexArray(right, i), that.array, loop.states, uuid)));
		return varLit;
	} else static if (is(T == Struct)) {
		if (that.values.length == 0) {
			return new JsLit("true");
		} else if (that.values.length == 1) {
			return compare(indexTuple(left, 0), indexTuple(right, 0),
					that.values[0], depend, uuid);
		}
		auto ret = new JsBinary!"&&"();
		auto current = ret;
		foreach (c, subType; that.values) {
			current.left = compare(indexTuple(left, c), indexTuple(right, c),
					subType, depend, uuid);
			if (c == that.values.length - 2) {
				current.right = compare(indexTuple(left, c + 1),
						indexTuple(right, c + 1), that.values[c + 1], depend, uuid);
				break;
			}
			auto next = new JsBinary!"&&"();
			current.right = next;
			current = next;
		}
		return ret;
	} else {
		static assert(0);
	}
}

JsExpr genTmp(JsExpr share, JsExpr init, ref JsState[] depend, ref uint uuid) {
	if (share) {
		if (init) {
			depend ~= new JsBinary!"="(share, init);
		}
	} else {
		auto name = genName(uuid);
		share = new JsLit(name);
		depend ~= new JsVarDef(name, init ? init : new JsLit("undefined"));
	}
	return share;
}

string escape(dchar d) {
	if (d == '\0') {
		return "\\0"; //"\0" in js
	} else if (d == '\'') {
		return "'";
	} else if (d == '"') {
		return "\\\""; //"\"" in js
	}
	return d.to!string;
}

enum Unique {
	copy,
	same
}

enum Eval {
	once,
	any,
	none
}

//the expression usage for generateJS
struct Usage {
	//if copy the value returned by the expression should have no aliases
	//if same the same reference must be returned each evaluatation
	Unique unique;
	//how many times is the expression going to be evaluated
	//if any then the result will be evaluated 0..n times
	//if once then the result will be evaluated once
	//if none then null must be returned
	Eval eval;
	//special case when eval and unique is false
	//if null is return the sub expression wrote the value to
	//a variable called share
	//otherwise normal behavior
	JsExpr share;
	invariant() {
		if (share) {
			assert(unique == Unique.same);
			assert(eval == Eval.once);
		}
	}

static:
	Usage container(Usage usage) {
		return Usage(Unique.copy, usage.eval);
	}

	Usage expression(Usage usage) {
		return Usage(usage.unique, usage.eval);
	}

	Usage literal() {
		return Usage(Unique.copy, Eval.any);
	}

	Usage variable() {
		return Usage(Unique.same, Eval.any);
	}

	Usage shareUsage(JsExpr share) {
		return Usage(Unique.same, Eval.once, share);
	}

	Usage once() {
		return Usage(Unique.same, Eval.once);
	}

	Usage none() {
		return Usage(Unique.same, Eval.none);
	}

	Usage copy() {
		return Usage(Unique.copy, Eval.any);
	}
}

JsExpr returnWrap(JsExpr result, Usage self, Usage request, Expression type,
		ref JsState[] depend, ref uint uuid) {
	if (self.eval == Eval.none) {
		assert(request.eval == Eval.none);
	}
	if (request.share && self.share) {
		assert(request.share == self.share);
		return null;
	}
	if (request.eval == Eval.none) {
		if (self.eval == Eval.once) {
			depend ~= result;
		}
		return null;
	}
	if (request.eval == Eval.once) {
		if (request.unique == Unique.copy && self.unique != Unique.copy) {
			return onceCopy(result, type, depend, uuid);
		}
		return result;
	}
	assert(request.eval == Eval.any);
	{
		if (self.eval == Eval.once) {
			auto ret = genTmp(null, result, depend, uuid);
			if (request.unique == Unique.copy) {
				return copy(ret, type);
			}
			return ret;
		}

		if (request.unique == Unique.copy && self.unique != Unique.copy) {
			return copy(result, type);
		}
		if (request.unique == Unique.same && self.unique != Unique.same) {
			auto ret = genTmp(null, result, depend, uuid);
			return ret;
		}
		assert(request.unique == self.unique);
		return result;
	}
}

void ignoreShare(ref Usage usage) {
	usage.share = null;
}

JsExpr symbolName(Var var) {
	return new JsLit(var.name);
}

JsExpr generateJS(Expression that, Trace* trace, Usage usage, ref JsState[] depend, ref uint uuid) {
	assert(isRuntimeValue(that));
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	return returnWrap(dispatch!(generateJSImpl, IntLit, BoolLit, CharLit, TupleLit,
			Variable, FuncArgument, If, While, New, NewArray, Cast, Dot, ArrayIndex,
			FCall, Slice, StringLit, ArrayLit, Binary!"==", Binary!"!=",
			Binary!"~", Prefix!"*", Prefix!"&", Scope, FuncLit, ExternJS,
			Binary!"*", Binary!"/", Binary!"%", Binary!"+", Binary!"-",
			Binary!"<=", Binary!">=", Binary!"<", Binary!">", Binary!"&&",
			Binary!"||", Prefix!"-", Prefix!"!")(that, trace, usage, depend, uuid).expand,
			usage, that.type, depend, uuid);
}

Tuple!(JsExpr, Usage) generateJSImpl(IntLit that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		return typeof(return)(new JsLit(value.to!string), Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(BoolLit that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		if (yes) {
			return typeof(return)(new JsLit("true"), Usage.literal);
		} else {
			return typeof(return)(new JsLit("false"), Usage.literal);
		}
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(CharLit that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		return typeof(return)(new JsLit('"' ~ escape(value) ~ '"'), Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(TupleLit that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		ignoreShare(usage);
		JsExpr[] exprs;
		exprs.length = values.length;
		foreach (i, field; values) {
			exprs[i] = generateJS(field, trace, Usage.container(usage), depend, uuid);
		}
		return typeof(return)(new JsArray(exprs), Usage.container(usage));
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Variable that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		JsExpr outvar = symbolName(that.definition);
		if (that.definition.heap) {
			outvar = new JsIndex(outvar, new JsLit("0"));
		}
		return typeof(return)(outvar, Usage.variable);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(FuncArgument that, Trace* trace,
		Usage usage, ref JsState[] depend, ref uint uuid) {
	with (that) {
		return typeof(return)(new JsLit("$argument"), Usage.variable);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(If that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto state = new JsIf();
		state.cond = generateJS(cond, trace, Usage.once, depend, uuid);
		if (usage.eval == Eval.none) {
			auto yes = generateJS(yes, trace, Usage.none, state.yes, uuid);
			auto no = generateJS(no, trace, Usage.none, state.no, uuid);
			depend ~= state;
			return typeof(return)(null, Usage.none);
		}

		auto tmp = genTmp(usage.share, null, depend, uuid);

		auto yesjs = generateJS(yes, trace, Usage.shareUsage(tmp), state.yes, uuid);
		auto nojs = generateJS(no, trace, Usage.shareUsage(tmp), state.no, uuid);

		if (yes) {
			state.yes ~= new JsBinary!"="(tmp, yesjs);
		}
		if (no) {
			state.no ~= new JsBinary!"="(tmp, nojs);
		}
		depend ~= state;
		return typeof(return)(tmp, Usage.variable);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(While that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		JsState[] condStates;
		auto cond = generateJS(cond, trace, Usage.once, condStates, uuid);
		auto state = new JsWhile();
		if (condStates.length == 0) {
			state.cond = cond;
			generateJS(that.state, trace, Usage.none, state.states, uuid);
		} else {
			state.cond = new JsLit("true");
			state.states ~= condStates;
			state.states ~= new JsIf(new JsPrefix!"!"(cond), [new JsBreak()], []);
			generateJS(that.state, trace, Usage.none, state.states, uuid);
		}
		depend ~= state;
		return typeof(return)(new JsArray([]), Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(New that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto ptr = new JsArray([generateJS(value, trace, Usage.container(usage), depend, uuid)]);
		return typeof(return)(ptr, Usage.container(usage));
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(NewArray that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto len = generateJS(length, trace, Usage.copy, depend, uuid);
		auto val = generateJS(value, trace, Usage.copy, depend, uuid);
		auto lit = genTmp(usage.share, new JsArray(), depend, uuid);
		auto loopInc = genName(uuid);
		auto incLit = new JsLit(loopInc);
		depend ~= new JsFor(new JsVarDef(loopInc, new JsLit("0")),
				new JsBinary!"<"(incLit, len), new JsPostfix!"++"(incLit),
				[new JsBinary!"="(new JsIndex(lit, incLit), val)]);
		return typeof(return)(lit, Usage.variable);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Cast that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		ignoreShare(usage);
		auto val = generateJS(value, trace, usage, depend, uuid);
		if (sameType(value.type, wanted)) {
			return typeof(return)(val, usage);
		} else if (sameType(value.type, createType!Struct())) {
			return typeof(return)(defaultValue(wanted), Usage.literal);
		} else if (cast(UInt) wanted.unalias || cast(Int) wanted.unalias) {
			return typeof(return)(castInt(val, wanted), usage);
		}
		assert(0);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Dot that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		ignoreShare(usage);
		if (variable) {
			return generateJSImpl(variable, trace, usage, depend, uuid);
		}
		auto val = generateJS(value, trace, usage, depend, uuid);
		JsExpr result;
		if (index.peek!string) {
			if (cast(ArrayIndex) value.type.unalias) {
				return typeof(return)(new JsDot(val, "length"), usage);
			}
			auto stru = cast(Struct)(value.type.unalias);
			result = indexTuple(val, stru.names[index.get!string]);
		} else {
			result = indexTuple(val, index.get!BigInt.to!size_t);
		}
		return typeof(return)(result, usage);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(ArrayIndex that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		ignoreShare(usage);
		auto array = generateJS(array, trace, Usage.copy, depend, uuid);
		auto index = generateJS(index, trace, usage, depend, uuid);
		auto result = indexArray(array, index);
		return typeof(return)(result, Usage.container(usage));
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(FCall that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto funcPtr = generateJS(fptr, trace, Usage.once, depend, uuid);
		auto arg = generateJS(arg, trace, Usage.copy, depend, uuid);
		auto expr = new JsCall(funcPtr, [arg]);
		return typeof(return)(expr, Usage.once);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Slice that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto array = generateJS(array, trace, Usage.copy, depend, uuid);
		auto left = generateJS(left, trace, Usage.copy, depend, uuid);
		auto right = generateJS(right, trace, Usage.copy, depend, uuid);
		auto expr = new JsObject([Tuple!(string, JsExpr)("data",
				internalArray(array)), Tuple!(string, JsExpr)("start",
				new JsBinary!"+"(arrayStart(array), left)), Tuple!(string,
				JsExpr)("length", new JsBinary!"-"(right, left))]);
		return typeof(return)(expr, Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(StringLit that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		string result;
		foreach (c; str) {
			result ~= escape(c);
		}
		auto expr = new JsCall(new JsDot(new JsLit("libtypi"),
				"jsStringToTypiString"), [new JsLit('"' ~ result ~ '"')]);
		return typeof(return)(expr, Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(ArrayLit that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto ret = new JsArray();
		foreach (val; values) {
			ret.exprs ~= generateJS(val, trace, Usage.copy, depend, uuid);
		}
		return typeof(return)(ret, Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Binary!"==" that, Trace* trace,
		Usage usage, ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto left = generateJS(left, trace, Usage.copy, depend, uuid);
		auto right = generateJS(right, trace, Usage.copy, depend, uuid);
		auto expr = compare(left, right, that.left.type, depend, uuid);
		return typeof(return)(expr, Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Binary!"!=" that, Trace* trace,
		Usage usage, ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto left = generateJS(left, trace, Usage.copy, depend, uuid);
		auto right = generateJS(right, trace, Usage.copy, depend, uuid);
		auto expr = new JsPrefix!"!"(compare(left, right, that.left.type, depend, uuid));
		return typeof(return)(expr, Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Binary!"~" that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto left = generateJS(left, trace, Usage.copy, depend, uuid);
		auto right = generateJS(right, trace, Usage.copy, depend, uuid);
		auto lit = genTmp(usage.share, new JsArray(), depend, uuid);
		auto i = new JsLit(genName(uuid));
		auto loop = new JsFor(new JsVarDef(i.value, new JsLit("0")),
				new JsBinary!"<"(i, arrayLength(left)), new JsPostfix!"++"(i), []);
		depend ~= loop;
		loop.states ~= new JsBinary!"="(new JsIndex(lit, i),
				copy(indexArray(left, i), (cast(ArrayIndex) that.left.type.unalias).array));
		auto loop2 = new JsFor(new JsVarDef(i.value, arrayLength(left)),
				new JsBinary!"<"(i, new JsBinary!"+"(arrayLength(left), arrayLength(right))),
				new JsPostfix!"++"(i), []);
		depend ~= loop;
		loop2.states ~= new JsBinary!"="(new JsIndex(lit, i),
				copy(indexArray(right, new JsBinary!"-"(i, arrayLength(left))),
					(cast(ArrayIndex) that.left.type.unalias).array));
		return typeof(return)(lit, Usage.variable);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Prefix!"*" that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		ignoreShare(usage);
		auto val = generateJS(value, trace, usage, depend, uuid);
		return typeof(return)(indexPointer(val), usage);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Prefix!"&" that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		return dispatch!(generateJSAddressOfImpl, Variable, Dot, ArrayIndex, Prefix!"*")(value,
				trace, usage, depend, uuid, type);
	}
}

Tuple!(JsExpr, Usage) generateJSAddressOfImpl(T)(T that, Trace* trace,
		Usage usage, ref JsState[] depend, ref uint uuid, Expression type) {
	auto nextTrace = Trace(that, trace);
	trace = &nextTrace;
	with (that)
		static if (is(T == Variable)) {
			JsExpr outvar = symbolName(that.definition);
			return typeof(return)(outvar, Usage.literal);
		} else static if (is(T == Dot)) {
			ignoreShare(usage);
			auto structType = cast(Struct) that.type.unalias;
			assert(structType);
			//todo bug, can't get address of .length
			auto structValue = generateJS(value, trace, usage, depend, uuid);
			size_t indexValue;
			if (index.peek!string) {
				indexValue = structType.names[index.get!string];
			} else {
				indexValue = index.get!BigInt.to!size_t;
			}
			auto expr = new JsObject([Tuple!(string, JsExpr)("data", structValue),
					Tuple!(string, JsExpr)("start", new JsLit(indexValue.to!string))]);
			return typeof(return)(expr, Usage.container(usage));
		} else static if (is(T == ArrayIndex)) {
			ignoreShare(usage);
			auto arr = generateJS(array, trace, Usage.copy, depend, uuid);
			auto index = generateJS(index, trace, usage, depend, uuid);
			auto expr = new JsObject([Tuple!(string, JsExpr)("data",
					internalArray(arr)), Tuple!(string, JsExpr)("start",
					new JsBinary!"+"(arrayStart(arr), index))]);
			return typeof(return)(expr, Usage.container(usage));
		} else static if (is(T == Prefix!"*")) {
			return typeof(return)(generateJS(value, trace, usage, depend, uuid), usage);
		} else {
			static assert(0);
		}
}

Tuple!(JsExpr, Usage) generateJSImpl(Scope that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		foreach (state; states) {
			if (auto val = cast(Expression) state) {
				generateJS(val, trace, Usage.none, depend, uuid);
			} else if (auto assign = cast(Assign) state) {
				depend ~= generateJSAssign(assign.left, assign.right, trace,
						Usage.once, depend, uuid);
			} else if (auto var = cast(ScopeVar) state) {
				auto val = generateJS(var.definition, trace, Usage(Unique.copy,
						Eval.once), depend, uuid);
				if (var.heap) {
					depend ~= new JsVarDef(var.name, new JsArray([val]));
				} else {
					depend ~= new JsVarDef(var.name, val);
				}
			} else {
				assert(0);
			}
			trace.context.pass(state);
		}
		ignoreShare(usage);
		auto result = generateJS(last, trace, usage, depend, uuid);
		return typeof(return)(result, usage);
	}
}

JsExpr generateJSAssign(Expression value, Expression rightValue, Trace* trace,
		Usage usage, ref JsState[] depend, ref uint uuid) {
	JsExpr outvar;
	ignoreShare(usage);
	auto right = generateJS(rightValue, trace, Usage.copy, depend, uuid);
	if (auto var = cast(Variable) value) {
		outvar = symbolName(var.definition);
		if (var.definition.heap) {
			outvar = new JsIndex(outvar, new JsLit("0"));
		}
		outvar = new JsBinary!"="(outvar, right);
	} else {
		auto sub = generateJS(value, trace, Usage.once, depend, uuid);
		outvar = new JsBinary!"="(sub, right);
	}
	return outvar;
}

Tuple!(JsExpr, Usage) generateJSImpl(FuncLit that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		auto result = new JsFuncLit(["$argument"], []);
		auto val = generateJS(text, trace, Usage(Unique.copy, Eval.once), result.states, uuid);

		if (!returns(result.states)) {
			result.states ~= new JsReturn(val);
		}
		return typeof(return)(result, Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(ExternJS that, Trace* trace, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	with (that) {
		return typeof(return)(new JsLit(external), Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(string op)(Binary!op that, Trace* trace,
		Usage usage, ref JsState[] depend, ref uint uuid)
		if (["*", "/", "%", "+", "-"].canFind(op)) {
	with (that) {
		ignoreShare(usage);
		auto left = generateJS(left, trace, usage, depend, uuid);
		auto right = generateJS(right, trace, usage, depend, uuid);
		return typeof(return)(castInt(new JsBinary!op(left, right), type), usage);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(string op)(Binary!op that, Trace* trace,
		Usage usage, ref JsState[] depend, ref uint uuid)
		if (["<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
	with (that) {
		ignoreShare(usage);
		auto left = generateJS(left, trace, usage, depend, uuid);
		auto right = generateJS(right, trace, usage, depend, uuid);
		return typeof(return)(new JsBinary!op(left, right), usage);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(string op)(Prefix!op that, Trace* trace,
		Usage usage, ref JsState[] depend, ref uint uuid) if (["-", "!"].canFind(op)) {
	with (that) {
		ignoreShare(usage);
		return typeof(return)(new JsPrefix!op(generateJS(value, trace, usage, depend, uuid)), usage);
	}
}
