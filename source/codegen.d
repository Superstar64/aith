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
import std.range : array, chain, drop, enumerate, only;
import std.stdio : write;
import std.string : front, popFront;
import std.typecons : Tuple, tuple;
import std.utf : encode;
import std.variant : visit;

import ast;
import error : error;
import semantic;
import jsast;

T castTo(T, Base)(Base node) {
	return cast(T) node;
}

//structs are repesented as native arrays
//arrays are either a native array or an object with a data, start, length, 
//pointers are arrays
//functions are native js functions

JsState[] generateJSModule(Module mod) {
	JsState[] result;
	foreach (symbol; mod.exports) {
		foreach (Type; SymbolTypes) {
			if (symbol.peek!Type) {
				auto that = *symbol.peek!Type;
				result ~= new JsVarDef(that.name, generateSymbol(that, result));
			}
		}
	}
	return result;
}

string genName(ref uint uuid) {
	auto vname = "$" ~ uuid.to!string;
	uuid++;
	return vname;
}

JsExpr generateSymbol(ModuleVarDef that, ref JsState[] depend) {
	uint uuid;
	if (that.heap) {
		return new JsArray([generateJS(that.definition, Usage.once, depend, uuid)]);
	} else {
		return generateJS(that.definition, Usage.once, depend, uuid);
	}
}

JsExpr generateSymbol(FuncLit that, ref JsState[] depend) {
	uint uuid;
	auto result = new JsFuncLit(["$argument"], []);
	auto val = generateJS(that.text, Usage(Unique.copy, Eval.once), result.states, uuid);
	result.states ~= new JsReturn(val);
	return result;
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
	return dispatch!(copyImpl, Bool, Char, Int, UInt, Postfix!"(*)",
			ArrayIndex, FuncCall, Struct)(type, expr);
}

JsExpr copyImpl(T)(T that, JsExpr expr) {
	static if (is(T == Bool) || is(T == Char) || is(T == Int) || is(T == UInt)
			|| is(T == Postfix!"(*)") || is(T == ArrayIndex) || is(T == FuncCall)) {
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

JsExpr onceCopy(JsExpr expr, Expression type, ref JsState[] depend, ref uint uuid) {
	return dispatch!(onceCopyImpl, Bool, Char, Int, UInt, Postfix!"(*)",
			ArrayIndex, FuncCall, Struct)(type, expr, depend, uuid);
}

JsExpr onceCopyImpl(T)(T that, JsExpr expr, ref JsState[] depend, ref uint uuid) {
	static if (is(T == Bool) || is(T == Char) || is(T == Int) || is(T == UInt)
			|| is(T == Postfix!"(*)") || is(T == ArrayIndex) || is(T == FuncCall)) {
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
			ArrayIndex, FuncCall, Struct)(type);
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
	} else static if (is(T == Postfix!"(*)") || is(T == FuncCall)) {
		return new JsLit("undefined");
	} else static if (is(T == ArrayIndex)) {
		return new JsArray();
	} else {
		static assert(0);
	}
}

JsExpr castInt(JsExpr expr, Expression type) {
	type = type;
	if (auto i = type.castTo!Int) {
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
	} else if (auto i = type.castTo!UInt) {
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

JsExpr compare(JsExpr left, JsExpr right, Expression type, ref JsState[] depend, ref uint uuid) {
	return dispatch!(compareImpl, Bool, Char, Int, UInt, FuncCall,
			Postfix!"(*)", ArrayIndex, Struct)(type, left, right, depend, uuid);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, ref JsState[] depend, ref uint uuid) {
	static if (is(T == Bool) || is(T == Char) || is(T == Int) || is(T == UInt) || is(T == FuncCall)) {
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

JsExpr symbolName(VarDef var) {
	return new JsLit(var.name);
}

JsExpr generateJS(Expression that, Usage usage, ref JsState[] depend, ref uint uuid) {
	assert(isRuntimeValue(that));
	return returnWrap(dispatch!(generateJSImpl, IntLit, BoolLit, CharLit, TupleLit,
			ScopeVarRef, ModuleVarRef, FuncArgument, If, While, New, NewArray, Cast, Dot,
			ArrayIndex, FuncCall, Slice, StringLit, ArrayLit, Binary!"==",
			Binary!"!=", Binary!"~", Prefix!"*", Prefix!"&", Scope, FuncLit,
			Binary!"*", Binary!"/", Binary!"%", Binary!"+", Binary!"-",
			Binary!"<=", Binary!">=", Binary!"<", Binary!">", Binary!"&&",
			Binary!"||", Prefix!"-", Prefix!"!", ExternJS)(that, usage, depend, uuid).expand,
			usage, that.type, depend, uuid);
}

Tuple!(JsExpr, Usage) generateJSImpl(IntLit that, Usage usage, ref JsState[] depend, ref uint uuid) {
	return typeof(return)(new JsLit(that.value.to!string), Usage.literal);
}

Tuple!(JsExpr, Usage) generateJSImpl(BoolLit that, Usage usage, ref JsState[] depend, ref uint uuid) {
	if (that.yes) {
		return typeof(return)(new JsLit("true"), Usage.literal);
	} else {
		return typeof(return)(new JsLit("false"), Usage.literal);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(CharLit that, Usage usage, ref JsState[] depend, ref uint uuid) {
	return typeof(return)(new JsLit('"' ~ escape(that.value) ~ '"'), Usage.literal);
}

Tuple!(JsExpr, Usage) generateJSImpl(TupleLit that, Usage usage, ref JsState[] depend, ref uint uuid) {
	ignoreShare(usage);
	JsExpr[] exprs;
	exprs.length = that.values.length;
	foreach (i, field; that.values) {
		exprs[i] = generateJS(field, Usage.container(usage), depend, uuid);
	}
	return typeof(return)(new JsArray(exprs), Usage.container(usage));
}

Tuple!(JsExpr, Usage) generateJSImpl(T)(T that, Usage usage, ref JsState[] depend, ref uint uuid)
		if (is(T == ScopeVarRef) || is(T == ModuleVarRef)) {
	JsExpr outvar = symbolName(that.definition);
	if (that.definition.heap) {
		outvar = new JsIndex(outvar, new JsLit("0"));
	}
	return typeof(return)(outvar, Usage.variable);
}

Tuple!(JsExpr, Usage) generateJSImpl(FuncArgument that, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	return typeof(return)(new JsLit("$argument"), Usage.variable);
}

Tuple!(JsExpr, Usage) generateJSImpl(If that, Usage usage, ref JsState[] depend, ref uint uuid) {
	auto state = new JsIf();
	state.cond = generateJS(that.cond, Usage.once, depend, uuid);
	if (usage.eval == Eval.none) {
		auto yes = generateJS(that.yes, Usage.none, state.yes, uuid);
		auto no = generateJS(that.no, Usage.none, state.no, uuid);
		depend ~= state;
		return typeof(return)(null, Usage.none);
	}

	auto tmp = genTmp(usage.share, null, depend, uuid);

	auto yesjs = generateJS(that.yes, Usage.shareUsage(tmp), state.yes, uuid);
	auto nojs = generateJS(that.no, Usage.shareUsage(tmp), state.no, uuid);

	if (that.yes) {
		state.yes ~= new JsBinary!"="(tmp, yesjs);
	}
	if (that.no) {
		state.no ~= new JsBinary!"="(tmp, nojs);
	}
	depend ~= state;
	return typeof(return)(tmp, Usage.variable);
}

Tuple!(JsExpr, Usage) generateJSImpl(While that, Usage usage, ref JsState[] depend, ref uint uuid) {
	JsState[] condStates;
	auto cond = generateJS(that.cond, Usage.once, condStates, uuid);
	auto state = new JsWhile();
	if (condStates.length == 0) {
		state.cond = cond;
		generateJS(that.state, Usage.none, state.states, uuid);
	} else {
		state.cond = new JsLit("true");
		state.states ~= condStates;
		state.states ~= new JsIf(new JsPrefix!"!"(cond), [new JsBreak()], []);
		generateJS(that.state, Usage.none, state.states, uuid);
	}
	depend ~= state;
	return typeof(return)(new JsArray([]), Usage.literal);
}

Tuple!(JsExpr, Usage) generateJSImpl(New that, Usage usage, ref JsState[] depend, ref uint uuid) {
	auto ptr = new JsArray([generateJS(that.value, Usage.container(usage), depend, uuid)]);
	return typeof(return)(ptr, Usage.container(usage));
}

Tuple!(JsExpr, Usage) generateJSImpl(NewArray that, Usage usage, ref JsState[] depend, ref uint uuid) {
	auto len = generateJS(that.length, Usage.copy, depend, uuid);
	auto val = generateJS(that.value, Usage.copy, depend, uuid);
	auto lit = genTmp(usage.share, new JsArray(), depend, uuid);
	auto loopInc = genName(uuid);
	auto incLit = new JsLit(loopInc);
	depend ~= new JsFor(new JsVarDef(loopInc, new JsLit("0")),
			new JsBinary!"<"(incLit, len), new JsPostfix!"++"(incLit),
			[new JsBinary!"="(new JsIndex(lit, incLit), val)]);
	return typeof(return)(lit, Usage.variable);
}

Tuple!(JsExpr, Usage) generateJSImpl(Cast that, Usage usage, ref JsState[] depend, ref uint uuid) {
	ignoreShare(usage);
	auto val = generateJS(that.value, usage, depend, uuid);
	if (sameType(that.value.type, that.wanted)) {
		return typeof(return)(val, usage);
	} else if (sameType(that.value.type, createType!Struct())) {
		return typeof(return)(defaultValue(that.wanted), Usage.literal);
	} else if (that.wanted.castTo!UInt || that.wanted.castTo!Int) {
		return typeof(return)(castInt(val, that.wanted), usage);
	} else if (that.value.castTo!ExternJS) {
		return typeof(return)(val, usage);
	}
	assert(0);
}

Tuple!(JsExpr, Usage) generateJSImpl(Dot that, Usage usage, ref JsState[] depend, ref uint uuid) {
	ignoreShare(usage);
	auto val = generateJS(that.value, usage, depend, uuid);
	assert(that.value.type.castTo!ArrayIndex);
	assert(that.index == "length");
	return typeof(return)(new JsDot(val, "length"), usage);
}

Tuple!(JsExpr, Usage) generateJSImpl(ArrayIndex that, Usage usage, ref JsState[] depend,
		ref uint uuid) {
	ignoreShare(usage);
	auto array = generateJS(that.array, Usage.copy, depend, uuid);
	if (that.array.type.castTo!ArrayIndex) {
		auto index = generateJS(that.index, usage, depend, uuid);
		auto result = indexArray(array, index);
		return typeof(return)(result, Usage.container(usage));
	} else {
		assert(that.array.type.castTo!Struct);
		auto index = that.index.castTo!IntLit.value.to!uint;
		auto result = indexTuple(array, index);
		return typeof(return)(result, usage);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(FuncCall that, Usage usage, ref JsState[] depend, ref uint uuid) {
	auto funcPtr = generateJS(that.fptr, Usage.once, depend, uuid);
	auto arg = generateJS(that.arg, Usage.copy, depend, uuid);
	auto expr = new JsCall(funcPtr, [arg]);
	return typeof(return)(expr, Usage.once);
}

Tuple!(JsExpr, Usage) generateJSImpl(Slice that, Usage usage, ref JsState[] depend, ref uint uuid) {
	auto array = generateJS(that.array, Usage.copy, depend, uuid);
	auto left = generateJS(that.left, Usage.copy, depend, uuid);
	auto right = generateJS(that.right, Usage.copy, depend, uuid);
	auto expr = new JsObject([Tuple!(string, JsExpr)("data",
			internalArray(array)), Tuple!(string, JsExpr)("start",
			new JsBinary!"+"(arrayStart(array), left)), Tuple!(string,
			JsExpr)("length", new JsBinary!"-"(right, left))]);
	return typeof(return)(expr, Usage.literal);
}

Tuple!(JsExpr, Usage) generateJSImpl(StringLit that, Usage usage, ref JsState[] depend, ref uint uuid) {
	return typeof(return)(new JsArray(that.str.map!(a => new JsLit('"' ~ [a].to!string ~ '"'))
			.map!(a => a.castTo!JsExpr).array), Usage.literal);
}

Tuple!(JsExpr, Usage) generateJSImpl(ArrayLit that, Usage usage, ref JsState[] depend, ref uint uuid) {
	auto ret = new JsArray();
	foreach (val; that.values) {
		ret.exprs ~= generateJS(val, Usage.copy, depend, uuid);
	}
	return typeof(return)(ret, Usage.literal);
}

Tuple!(JsExpr, Usage) generateJSImpl(Binary!"==" that, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	auto left = generateJS(that.left, Usage.copy, depend, uuid);
	auto right = generateJS(that.right, Usage.copy, depend, uuid);
	auto expr = compare(left, right, that.left.type, depend, uuid);
	return typeof(return)(expr, Usage.literal);
}

Tuple!(JsExpr, Usage) generateJSImpl(Binary!"!=" that, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	auto left = generateJS(that.left, Usage.copy, depend, uuid);
	auto right = generateJS(that.right, Usage.copy, depend, uuid);
	auto expr = new JsPrefix!"!"(compare(left, right, that.left.type, depend, uuid));
	return typeof(return)(expr, Usage.literal);
}

Tuple!(JsExpr, Usage) generateJSImpl(Binary!"~" that, Usage usage, ref JsState[] depend,
		ref uint uuid) {
	auto left = generateJS(that.left, Usage.copy, depend, uuid);
	auto right = generateJS(that.right, Usage.copy, depend, uuid);
	auto lit = genTmp(usage.share, new JsArray(), depend, uuid);
	auto i = new JsLit(genName(uuid));
	auto loop = new JsFor(new JsVarDef(i.value, new JsLit("0")),
			new JsBinary!"<"(i, arrayLength(left)), new JsPostfix!"++"(i), []);
	depend ~= loop;
	loop.states ~= new JsBinary!"="(new JsIndex(lit, i), copy(indexArray(left,
			i), that.left.type.castTo!ArrayIndex.array));
	auto loop2 = new JsFor(new JsVarDef(i.value, arrayLength(left)),
			new JsBinary!"<"(i, new JsBinary!"+"(arrayLength(left), arrayLength(right))),
			new JsPostfix!"++"(i), []);
	depend ~= loop;
	loop2.states ~= new JsBinary!"="(new JsIndex(lit, i), copy(indexArray(right,
			new JsBinary!"-"(i, arrayLength(left))), that.left.type.castTo!ArrayIndex.array));
	return typeof(return)(lit, Usage.variable);
}

Tuple!(JsExpr, Usage) generateJSImpl(Prefix!"*" that, Usage usage, ref JsState[] depend,
		ref uint uuid) {
	ignoreShare(usage);
	auto val = generateJS(that.value, usage, depend, uuid);
	return typeof(return)(indexPointer(val), usage);
}

Tuple!(JsExpr, Usage) generateJSImpl(Prefix!"&" that, Usage usage, ref JsState[] depend,
		ref uint uuid) {
	return dispatch!(generateJSAddressOfImpl, ScopeVarRef, ModuleVarRef, Dot,
			ArrayIndex, Prefix!"*")(that.value, usage, depend, uuid, that.type);
}

Tuple!(JsExpr, Usage) generateJSAddressOfImpl(T)(T that, Usage usage,
		ref JsState[] depend, ref uint uuid, Expression type) {
	static if (is(T == ScopeVarRef) || is(T == ModuleVarRef)) {
		JsExpr outvar = symbolName(that.definition);
		return typeof(return)(outvar, Usage.literal);
	} else static if (is(T == Dot)) {
		error("trying to take address of .length", that.pos);
		assert(0);
		ignoreShare(usage);

	} else static if (is(T == ArrayIndex)) {
		if (that.array.type.castTo!ArrayIndex) {
			auto arr = generateJS(that.array, Usage.copy, depend, uuid);
			auto index = generateJS(that.index, usage, depend, uuid);
			auto expr = new JsObject([Tuple!(string, JsExpr)("data",
					internalArray(arr)), Tuple!(string, JsExpr)("start",
					new JsBinary!"+"(arrayStart(arr), index))]);
			return typeof(return)(expr, Usage.container(usage));
		} else {
			auto structType = that.type.castTo!Struct;
			assert(structType);
			auto structValue = generateJS(that.array, usage, depend, uuid);
			size_t indexValue = that.index.castTo!IntLit.value.to!uint;
			auto expr = new JsObject([Tuple!(string, JsExpr)("data", structValue),
					Tuple!(string, JsExpr)("start", new JsLit(indexValue.to!string))]);
			return typeof(return)(expr, Usage.container(usage));
		}
	} else static if (is(T == Prefix!"*")) {
		return typeof(return)(generateJS(that.value, usage, depend, uuid), usage);
	} else {
		static assert(0);
	}
}

Tuple!(JsExpr, Usage) generateJSImpl(Scope that, Usage usage, ref JsState[] depend, ref uint uuid) {
	foreach (state; that.states) {
		if (auto val = state.castTo!Expression) {
			generateJS(val, Usage.none, depend, uuid);
		} else if (auto assign = state.castTo!Assign) {
			depend ~= generateJSAssign(assign.left, assign.right, Usage.once, depend, uuid);
		} else if (auto var = state.castTo!ScopeVarDef) {
			auto val = generateJS(var.definition, Usage(Unique.copy, Eval.once), depend, uuid);
			if (var.heap) {
				depend ~= new JsVarDef(var.name, new JsArray([val]));
			} else {
				depend ~= new JsVarDef(var.name, val);
			}
		} else {
			assert(0);
		}
	}
	ignoreShare(usage);
	auto result = generateJS(that.last, usage, depend, uuid);
	return typeof(return)(result, usage);
}

JsExpr generateJSAssign(Expression value, Expression rightValue, Usage usage,
		ref JsState[] depend, ref uint uuid) {
	JsExpr outvar;
	ignoreShare(usage);
	auto right = generateJS(rightValue, Usage.copy, depend, uuid);
	auto sub = generateJS(value, Usage.once, depend, uuid);
	outvar = new JsBinary!"="(sub, right);
	return outvar;
}

Tuple!(JsExpr, Usage) generateJSImpl(FuncLit that, Usage usage, ref JsState[] depend, ref uint uuid) {
	return typeof(return)(new JsLit(that.name), Usage.variable);
}

Tuple!(JsExpr, Usage) generateJSImpl(string op)(Binary!op that, Usage usage,
		ref JsState[] depend, ref uint uuid)
		if (["*", "/", "%", "+", "-"].canFind(op)) {
	ignoreShare(usage);
	auto left = generateJS(that.left, usage, depend, uuid);
	auto right = generateJS(that.right, usage, depend, uuid);
	return typeof(return)(castInt(new JsBinary!op(left, right), that.type), usage);
}

Tuple!(JsExpr, Usage) generateJSImpl(string op)(Binary!op that, Usage usage,
		ref JsState[] depend, ref uint uuid)
		if (["<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
	ignoreShare(usage);
	auto left = generateJS(that.left, usage, depend, uuid);
	auto right = generateJS(that.right, usage, depend, uuid);
	return typeof(return)(new JsBinary!op(left, right), usage);
}

Tuple!(JsExpr, Usage) generateJSImpl(string op)(Prefix!op that, Usage usage,
		ref JsState[] depend, ref uint uuid) if (["-", "!"].canFind(op)) {
	ignoreShare(usage);
	return typeof(return)(new JsPrefix!op(generateJS(that.value, usage, depend, uuid)), usage);
}

Tuple!(JsExpr, Usage) generateJSImpl(ExternJS that, Usage usage, ref JsState[] depend, ref uint uuid) {
	return typeof(return)(new JsLit(that.name), Usage.variable);
}
