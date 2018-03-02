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

import std.algorithm : canFind, each, find, filter, map;
import std.array : join, empty, popBack;
import std.bigint : BigInt;
import std.conv : to;
import std.meta : AliasSeq, staticIndexOf;
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
//struct are copied on caller side and on return

//arrays are either a native array or an object with a data, start, length
//pointers objects with type,get,and set
//the pointer types are 'local,'array' and 'tuple'
//functions are native js functions

JsModule generateJsModule(Module mod) {
	JsModule result = new JsModule();
	Extra extra;
	foreach (symbol; mod.exports) {
		foreach (Type; SymbolTypes) {
			if (symbol.peek!Type) {
				auto that = symbol.get!Type;
				result ~= new JsVarDef(that.name, generateSymbol(that, result, &extra));
			}
		}
	}
	applyGlobalRequests(result, &extra);
	return result;
}

void applyGlobalRequests(JsScope depend, Extra* extra) {
	void applyRequest(ref Expression[] array, JsFuncLit function(Expression,
			Extra*) create, string prefix) {
		while (array.length) {
			depend ~= new JsVarDef(prefix ~ mangle(array[$ - 1]), create(array[$ - 1], extra));
			array.popBack;
		}
	}

	applyRequest(extra.copyFunctions, &createCopy, "__copy_");
	applyRequest(extra.compareFunctions, &createCompare, "__compare_");
}

JsExpr generateSymbol(ModuleVarDef that, JsScope depend, Extra* extra) {
	extra.context = FunctionContext();
	return generateJs(that.definition, Usage(true, Case.copyObject), depend, extra);
}

JsExpr generateSymbol(FuncLit that, JsScope depend, Extra* extra) {
	extra.context = FunctionContext();
	extra.context.argumentName = genName(extra);
	auto result = new JsFuncLit([extra.context.argumentName], []);
	if (!sameType(that.text.type, createType!Struct())) {
		auto val = generateJs(that.text, Usage(true, Case.copyObject), result.states, extra);
		result.states ~= new JsReturn(val);
	} else {
		generateJsEffectsOnly(that.text, result.states, extra);
	}

	return result;
}

enum Case {
	copyObject,
	accessField
}

struct Usage {
	//if false side effects must be dumped into it's scope
	bool sideEffects;
	//in javascript object are copy be reference
	//structs are copy by value so objects need to be implicitly copied if needed
	Case useCase;
}

struct FunctionContext {
	JsLit[ScopeVarDef] localPointers;
	JsScope[ScopeVarDef] variableScopes;

	string argumentName;
}

struct Extra {
	uint uuid;
	FunctionContext context;

	JsLit[ModuleVarDef] globalPointers;

	//todo make types usable in hash maps

	//expression is the type
	Expression[] copyFunctions;

	Expression[] compareFunctions;
}

JsExpr symbolName(VarDef var, Extra* extra) {
	return new JsLit(var.name);
}

string genName(Extra* extra) {
	auto identifier = "$" ~ extra.uuid.to!string;
	extra.uuid++;
	return identifier;
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

JsExpr getPointer(JsExpr pointer) {
	return new JsCall(new JsDot(pointer, "get"), []);
}

JsExpr setPointer(JsExpr pointer, JsExpr value) {
	return new JsCall(new JsDot(pointer, "set"), [value]);
}

JsExpr createLocalPointer(JsExpr variable) {
	return new JsObject([Tuple!(string, JsExpr)("type", new JsLit("'local'")),
			Tuple!(string, JsExpr)("get", new JsFuncLit([], [new JsReturn(variable)])), Tuple!(string, JsExpr)("set",
				new JsFuncLit(["value"], [new JsBinary!"="(variable, new JsLit("value"))]))]);
}

string mangle(Expression type) {
	return dispatch!(mangleImpl, Bool, Char, Int, UInt, Struct, Postfix!"(*)",
			ArrayIndex, FuncCall)(type);
}

string mangleImpl(Bool type) {
	return "bool";
}

string mangleImpl(Char type) {
	return "char";
}

string mangleImpl(Int type) {
	return "int" ~ type.size.to!string;
}

string mangleImpl(UInt type) {
	return "uint" ~ type.size.to!string;
}

string mangleImpl(Struct type) {
	return "struct$" ~ type.values.map!mangle.map!(a => a ~ "_").joiner.array.to!string ~ "$";
}

string mangleImpl(Postfix!"(*)" type) {
	return type.value.mangle ~ "_pointer";
}

string mangleImpl(ArrayIndex type) {
	return type.array.mangle ~ "_array";
}

string mangleImpl(FuncCall type) {
	return "function$" ~ type.fptr.mangle ~ "$" ~ type.arg.mangle ~ "$";
}

JsExpr copy(JsExpr expr, Expression type, Extra* extra) {
	return dispatch!(copyImpl, Bool, Char, Int, UInt, Struct, Postfix!"(*)",
			ArrayIndex, FuncCall)(type, expr, extra);
}

JsExpr copyImpl(T)(T, JsExpr expr, Extra*)
		if (staticIndexOf!(T, Bool, Char, Int, UInt, Postfix!"(*)", ArrayIndex, FuncCall) >= 0) {
	return expr;
}

JsExpr copyImpl(Struct that, JsExpr expr, Extra* extra) {
	if (that.values.length == 0) {
		return expr;
	}
	auto range = extra.copyFunctions.find!sameType(that);
	if (range.empty) {
		extra.copyFunctions ~= that;
	}
	return new JsCall(new JsLit("__copy_" ~ mangle(that)), [expr]);
}

JsFuncLit createCopy(Expression type, Extra* extra) {
	assert(type.castTo!Struct);
	auto Struct = type.castTo!Struct;
	auto argumentName = genName(extra);
	return new JsFuncLit([argumentName],
			[new JsReturn(new JsArray(Struct.values.enumerate.map!(a => copy(indexTuple(new JsLit(argumentName),
				a[0]), a[1], extra)).array))]);
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

JsExpr compare(JsExpr left, JsExpr right, Expression type, Extra* extra) {
	return dispatch!(compareImpl, Bool, Char, Int, UInt, FuncCall,
			Postfix!"(*)", ArrayIndex, Struct)(type, left, right, extra);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, Extra* extra)
		if (staticIndexOf!(T, Bool, Char, Int, UInt, FuncCall) >= 0) {
	return new JsBinary!"=="(left, right);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, Extra* extra)
		if (staticIndexOf!(T, Postfix!"(*)", ArrayIndex, Struct) >= 0) {
	auto range = extra.compareFunctions.find!sameType(that);
	if (range.empty) {
		extra.compareFunctions ~= that;
	}
	return new JsCall(new JsLit("__compare_" ~ mangle(that)), [left, right]);
}

JsFuncLit createCompare(Expression that, Extra* extra) {
	auto Function = new JsFuncLit(["left", "right"], []);
	dispatch!(createCompareImpl, Postfix!"(*)", ArrayIndex, Struct)(that,
			new JsLit("left"), new JsLit("right"), Function.states, extra);
	return Function;
}

void createCompareImpl(Postfix!"(*)" that, JsExpr left, JsExpr right, JsScope depend, Extra* extra) {
	auto If = new JsIf(new JsBinary!"!="(new JsDot(left, "type"),
			new JsDot(right, "type")), [new JsReturn(new JsLit("false"))], []);
	depend ~= If;
	auto localIf = new JsIf(new JsBinary!"=="(new JsDot(left, "type"),
			new JsLit("'local'")), [new JsReturn(new JsBinary!"=="(left, right))], []);
	depend ~= localIf;
	auto arrayCompare = new JsBinary!"&&"(new JsBinary!"=="(internalArray(new JsDot(left,
			"array")), internalArray(new JsDot(right, "array"))),
			new JsBinary!"=="(new JsDot(left, "index"), new JsDot(right, "index")));
	auto arrayIf = new JsIf(new JsBinary!"=="(new JsDot(left, "type"),
			new JsLit("'array'")), [new JsReturn(arrayCompare)], []);
	localIf.no ~= arrayIf;
	auto tupleCompare = new JsBinary!"&&"(new JsCall(new JsLit("__compare_" ~ mangle(that)),
			[new JsDot(left, "pointer"), new JsDot(right, "pointer")]),
			new JsBinary!"=="(new JsDot(left, "index"), new JsDot(right, "index")));
	auto tupleIf = new JsIf(new JsBinary!"=="(new JsDot(left, "type"),
			new JsLit("'tuple'")), [new JsReturn(tupleCompare)], []);
	arrayIf.no ~= tupleIf;
}

void createCompareImpl(ArrayIndex that, JsExpr left, JsExpr right, JsScope depend, Extra* extra) {
	auto lengthCompare = new JsBinary!"!="(arrayLength(left), arrayLength(right));
	depend.states ~= new JsIf(lengthCompare, [new JsReturn(new JsLit("false"))], []);

	auto iterator = new JsLit(genName(extra));
	auto For = new JsFor(new JsVarDef(iterator.value, new JsLit("0")),
			new JsBinary!"<"(iterator, arrayLength(left)), new JsPostfix!"++"(iterator), []);
	depend ~= For;

	auto elementComparer = new JsPrefix!"!"(compare(indexArray(left, iterator),
			indexArray(right, iterator), that.array, extra));

	For.states ~= new JsIf(elementComparer, [new JsReturn(new JsLit("false"))], []);

	depend ~= new JsReturn(new JsLit("true"));
}

void createCompareImpl(Struct that, JsExpr left, JsExpr right, JsScope depend, Extra* extra) {
	if (that.values.length == 0) {
		depend ~= new JsReturn(new JsLit("true"));
	}
	depend ~= new JsReturn(createCompareImplStruct(0, that, left, right, depend, extra));
}

JsExpr createCompareImplStruct(uint index, Struct that, JsExpr left, JsExpr right,
		JsScope depend, Extra* extra) {
	auto head = compare(indexTuple(left, index), indexTuple(right, index),
			that.values[index], extra);
	if (index + 1 == that.values.length) {
		return head;
	} else {
		return new JsBinary!"&&"(head, createCompareImplStruct(index + 1, that,
				left, right, depend, extra));
	}
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

JsExpr maybeCopy(JsExpr expression, Expression type, Usage usage, Extra* extra) {
	if (usage.useCase == Case.copyObject) {
		return copy(expression, type, extra);
	} else {
		return expression;
	}
}

alias Nodes = AliasSeq!(IntLit, BoolLit, CharLit, TupleLit, ScopeVarRef, ModuleVarRef,
		FuncArgument, If, While, New, NewArray, Cast, Dot, ArrayIndex, FuncCall,
		Slice, StringLit, ArrayLit, Binary!"==", Binary!"!=", Binary!"~",
		Prefix!"*", Prefix!"&", Scope, FuncLit, Binary!"*", Binary!"/",
		Binary!"%", Binary!"+", Binary!"-", Binary!"<=", Binary!">=",
		Binary!"<", Binary!">", Binary!"&&", Binary!"||", Prefix!"-", Prefix!"!", ExternJs);

JsExpr generateJs(Expression that, Usage usage, JsScope depend, Extra* extra) {
	assert(isRuntimeValue(that));
	return dispatch!(generateJsImpl, Nodes)(that, usage, depend, extra);
}

JsState assignTo(bool createVar, JsLit left, JsExpr right) {
	if (createVar) {
		return new JsVarDef(left.value, right);
	} else {
		return new JsBinary!"="(left, right);
	}
}

void generateJsIntoVar(Expression that, JsLit variable, bool createVar,
		Case shouldCopy, JsScope depend, Extra* extra) {
	assert(isRuntimeValue(that));
	return dispatch!(generateJsIntoVarImpl, Nodes)(that, variable, createVar,
			shouldCopy, depend, extra);
}

//todo print warning if unusal node(new,intlit,etc)
void generateJsEffectsOnly(Expression that, JsScope depend, Extra* extra) {
	assert(isRuntimeValue(that));
	return dispatch!(generateJsEffectsOnlyImpl, Nodes)(that, depend, extra);
}

//only have a generateinto
alias VariableOutput = AliasSeq!(If, NewArray);

JsExpr generateJsImpl(T)(T that, Usage usage, JsScope depend, Extra* extra)
		if (staticIndexOf!(T, VariableOutput) >= 0) {
	return createVarAndGenerateInto(that, usage, depend, extra);
}

JsExpr createVarAndGenerateInto(T)(T that, Usage usage, JsScope depend, Extra* extra) {
	auto variable = new JsLit(genName(extra));
	generateJsIntoVarImpl(that, variable, true, Case.accessField, depend, extra);
	return maybeCopy(variable, that.type, usage, extra);
}

void generateJsIntoVarImpl(T)(T that, JsLit variable, bool createVar,
		Case shouldCopy, JsScope depend, Extra* extra)
		if (staticIndexOf!(T, VariableOutput) < 0) {
	depend ~= assignTo(createVar, variable, generateJs(that, Usage(true,
			shouldCopy), depend, extra));
}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra* extra)
		if (staticIndexOf!(T, IntLit, BoolLit, CharLit, ScopeVarRef,
			ModuleVarRef, FuncArgument, StringLit, FuncLit, ExternJs) >= 0) {

}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra* extra)
		if (staticIndexOf!(T, New, Cast, Dot, Prefix!"+", Prefix!"-",
			Prefix!"*", Prefix!"/", Prefix!"&", Prefix!"!") >= 0) {
	generateJsEffectsOnly(that.value, depend, extra);
}

void generateJsEffectsOnlyImpl(string op)(Binary!op that, JsScope depend, Extra* extra) {
	generateJsEffectsOnly(that.left, depend, extra);
	generateJsEffectsOnly(that.right, depend, extra);
}

JsExpr generateJsImpl(IntLit that, Usage usage, JsScope depend, Extra* extra) {
	return new JsLit(that.value.to!string);
}

JsExpr generateJsImpl(BoolLit that, Usage usage, JsScope depend, Extra* extra) {
	if (that.yes) {
		return new JsLit("true");
	} else {
		return new JsLit("false");
	}
}

JsExpr generateJsImpl(CharLit that, Usage usage, JsScope depend, Extra* extra) {
	return new JsLit('"' ~ escape(that.value) ~ '"');
}

JsExpr generateJsImpl(TupleLit that, Usage usage, JsScope depend, Extra* extra) {
	return new JsArray(that.values.map!(a => generateJs(a, usage, depend, extra)).array);
}

void generateJsEffectsOnlyImpl(TupleLit that, JsScope depend, Extra* extra) {
	return that.values.each!(a => generateJsEffectsOnly(a, depend, extra));
}

JsExpr generateJsImpl(T)(T that, Usage usage, JsScope depend, Extra* extra)
		if (is(T == ScopeVarRef) || is(T == ModuleVarRef)) {
	return maybeCopy(symbolName(that.definition, extra), that.type, usage, extra);
}

JsExpr generateJsImpl(FuncArgument that, Usage usage, JsScope, Extra* extra) {
	return maybeCopy(new JsLit(extra.context.argumentName), that.type, usage, extra);
}

void generateJsIntoVarImpl(If that, JsLit variable, bool createVar,
		Case shouldCopy, JsScope depend, Extra* extra) {
	auto If = new JsIf();
	if (createVar) {
		depend ~= assignTo(true, variable, new JsLit("undefined"));
	}
	If.cond = generateJs(that.cond, Usage(true), depend, extra);
	generateJsIntoVar(that.yes, variable, false, shouldCopy, If.yes, extra);
	generateJsIntoVar(that.no, variable, false, shouldCopy, If.no, extra);
	depend ~= If;
}

void generateJsEffectsOnlyImpl(If that, JsScope depend, Extra* extra) {
	auto If = new JsIf();
	If.cond = generateJs(that.cond, Usage(true), depend, extra);
	generateJsEffectsOnly(that.yes, If.yes, extra);
	generateJsEffectsOnly(that.no, If.no, extra);
	depend ~= If;
}

JsExpr generateJsImpl(While that, Usage usage, JsScope depend, Extra* extra) {
	auto While = new JsWhile();
	auto cond = generateJs(that.cond, Usage(true), While.states, extra);

	if (While.states.length == 0) {
		While.cond = cond;
		generateJsEffectsOnly(that.state, While.states, extra);
	} else {
		While.cond = new JsLit("true");
		While.states ~= new JsIf(new JsPrefix!"!"(cond), [new JsBreak()], []);
		generateJsEffectsOnly(that.state, While.states, extra);
	}
	depend ~= While;
	return new JsArray([]);
}

void generateJsEffectsOnlyImpl(While that, JsScope depend, Extra* extra) {
	generateJsImpl(that, Usage(), depend, extra);
}

JsExpr generateJsImpl(New that, Usage usage, JsScope depend, Extra* extra) {
	auto local = new JsLit(genName(extra));
	generateJsIntoVar(that.value, local, true, Case.copyObject, depend, extra);
	if (usage.sideEffects) {
		return createLocalPointer(local);
	} else {
		return createVarAndGenerateInto(that, Usage(true), depend, extra);
	}
}

void generateJsIntoVarImpl(NewArray that, JsLit variable, bool createVar,
		Case shouldCopy, JsScope depend, Extra* extra) {
	auto length = generateJs(that.length, Usage(false), depend, extra);
	auto expression = generateJs(that.value, Usage(false, Case.copyObject), depend, extra);

	depend ~= assignTo(createVar, variable, new JsArray());
	auto iterator = new JsLit(genName(extra));
	depend ~= new JsFor(new JsVarDef(iterator.value, new JsLit("0")),
			new JsBinary!"<"(iterator, length), new JsPostfix!"++"(iterator),
			[new JsBinary!"="(new JsIndex(variable, iterator), expression)]);
}

void generateJsEffectsOnlyImpl(NewArray that, JsScope depend, Extra* extra) {
	generateJsEffectsOnly(that.value, depend, extra);
	generateJsEffectsOnly(that.length, depend, extra);
}

JsExpr generateJsImpl(Cast that, Usage usage, JsScope depend, Extra* extra) {
	auto value = generateJs(that.value, usage, depend, extra);
	if (sameType(that.value.type, that.wanted)) {
		return value;
	} else if (sameType(that.value.type, createType!Struct())) {
		return maybeCopy(defaultValue(that.wanted), that.wanted, usage, extra);
	} else if (that.wanted.castTo!UInt || that.wanted.castTo!Int) {
		if (that.implicit) {
			return value;
		}
		return castInt(value, that.wanted);
	} else if (that.value.castTo!ExternJs) {
		return value;
	}
	assert(0);
}

JsExpr generateJsImpl(Dot that, Usage usage, JsScope depend, Extra* extra) {
	auto value = generateJs(that.value, usage, depend, extra);
	assert(that.value.type.castTo!ArrayIndex);
	assert(that.index == "length");
	return arrayLength(value);
}

JsExpr generateJsImpl(ArrayIndex that, Usage usage, JsScope depend, Extra* extra) {
	if (that.array.type.castTo!ArrayIndex) {
		auto array = generateJs(that.array, Usage(false), depend, extra);
		auto index = generateJs(that.index, Usage(false), depend, extra);
		return indexArray(array, index);
	} else {
		auto array = generateJs(that.array, usage, depend, extra);
		assert(that.array.type.castTo!Struct);
		auto index = that.index.castTo!IntLit.value.to!uint;
		return indexTuple(array, index);
	}
}

void generateJsEffectsOnlyImpl(ArrayIndex that, JsScope depend, Extra* extra) {
	generateJsEffectsOnly(that.array, depend, extra);
	generateJsEffectsOnly(that.index, depend, extra);
}

JsExpr generateJsImpl(FuncCall that, Usage usage, JsScope depend, Extra* extra) {
	if (usage.sideEffects) {
		auto functionPointer = generateJs(that.fptr, Usage(true), depend, extra);
		auto argument = generateJs(that.arg, Usage(true, Case.copyObject), depend, extra);
		auto expression = new JsCall(functionPointer, [argument]);
		return expression;
	} else {
		return createVarAndGenerateInto(that, Usage(true, Case.copyObject), depend, extra);
	}
}

void generateJsEffectsOnlyImpl(FuncCall that, JsScope depend, Extra* extra) {
	auto functionPointer = generateJs(that.fptr, Usage(true), depend, extra);
	auto argument = generateJs(that.arg, Usage(true, Case.copyObject), depend, extra);
	depend ~= new JsCall(functionPointer, [argument]);
}

JsExpr generateJsImpl(Slice that, Usage usage, JsScope depend, Extra* extra) {
	auto array = generateJs(that.array, Usage(false), depend, extra);
	auto left = generateJs(that.left, Usage(false), depend, extra);
	auto right = generateJs(that.right, Usage(false), depend, extra);
	return new JsObject([Tuple!(string, JsExpr)("data", internalArray(array)),
			Tuple!(string, JsExpr)("start", new JsBinary!"+"(arrayStart(array), left)),
			Tuple!(string, JsExpr)("length", new JsBinary!"-"(right, left))]);
}

void generateJsEffectsOnlyImpl(Slice that, JsScope depend, Extra* extra) {
	generateJsEffectsOnly(that.array, depend, extra);
	generateJsEffectsOnly(that.left, depend, extra);
	generateJsEffectsOnly(that.right, depend, extra);
}

JsExpr generateJsImpl(StringLit that, Usage usage, JsScope depend, Extra* extra) {
	return new JsArray(that.str.map!(a => new JsLit('"' ~ [a].to!string ~ '"')).map!(
			a => a.castTo!JsExpr).array);
}

JsExpr generateJsImpl(ArrayLit that, Usage usage, JsScope depend, Extra* extra) {
	if (usage.sideEffects) {
		return new JsArray(that.values.map!(a => generateJs(a, Usage(true,
				Case.copyObject), depend, extra)).array);
	} else {
		return createVarAndGenerateInto(that, Usage(false), depend, extra);
	}
}

void generateJsEffectsOnlyImpl(ArrayLit that, JsScope depend, Extra* extra) {
	that.values.each!(a => generateJsEffectsOnly(that, depend, extra));
}

JsExpr generateJsImpl(Binary!"==" that, Usage usage, JsScope depend, Extra* extra) {
	auto left = generateJs(that.left, Usage(usage.sideEffects, Case.accessField), depend, extra);
	auto right = generateJs(that.right, Usage(usage.sideEffects, Case.accessField), depend, extra);
	return compare(left, right, that.left.type, extra);
}

JsExpr generateJsImpl(Binary!"!=" that, Usage usage, JsScope depend, Extra* extra) {
	auto left = generateJs(that.left, Usage(usage.sideEffects, Case.accessField), depend, extra);
	auto right = generateJs(that.right, Usage(usage.sideEffects, Case.accessField), depend, extra);
	return new JsPrefix!"!"(compare(left, right, that.left.type, extra));
}

JsExpr generateJsImpl(Binary!"~" that, Usage usage, JsScope depend, Extra* extra) {
	assert(0, "todo implement ~");
}

JsExpr generateJsImpl(Prefix!"*" that, Usage usage, JsScope depend, Extra* extra) {
	return getPointer(generateJs(that.value, usage, depend, extra));
}

JsExpr generateJsImpl(Prefix!"&" that, Usage usage, JsScope depend, Extra* extra) {
	return dispatch!(generateJsAddressOfImpl, ScopeVarRef, ModuleVarRef, ArrayIndex, Prefix!"*")(
			that.value, usage, depend, extra);
}

JsExpr generateJsAddressOfImpl(ScopeVarRef that, Usage usage, JsScope depend, Extra* extra) {
	if (that.definition in extra.context.localPointers) {
		return extra.context.localPointers[that.definition];
	}
	auto pointer = new JsLit(genName(extra));
	extra.context.variableScopes[that.definition] ~= new JsVarDef(pointer.value,
			createLocalPointer(new JsLit(that.definition.name)));
	extra.context.localPointers[that.definition] = pointer;
	return pointer;
}

JsExpr generateJsAddressOfImpl(ModuleVarRef that, Usage usage, JsScope depend, Extra* extra) {
	assert(0, "todo implement module pointers");
}

JsExpr generateJsAddressOfImpl(ArrayIndex that, Usage usage, JsScope depend, Extra* extra) {
	enum dotThis = (string expression) => new JsDot(new JsLit("this"), expression);
	if (that.array.type.castTo!ArrayIndex) {
		auto array = generateJs(that.array, usage, depend, extra);
		auto index = generateJs(that.index, usage, depend, extra);

		return new JsObject([Tuple!(string, JsExpr)("type",
				new JsLit("'array'")), Tuple!(string, JsExpr)("array", array),
				Tuple!(string, JsExpr)("index", index), Tuple!(string, JsExpr)("get",
					new JsFuncLit([], [new JsReturn(indexArray(dotThis("array"),
					dotThis("index")))])), Tuple!(string, JsExpr)("set", new JsFuncLit(["value"],
					[new JsBinary!"="(indexArray(dotThis("array"),
					dotThis("index")), new JsLit("value"))]))]);
	} else {
		auto structType = that.array.type.castTo!Struct;
		assert(structType);
		auto tuplePointer = dispatch!(generateJsAddressOfImpl, ScopeVarRef,
				ModuleVarRef, ArrayIndex, Prefix!"*")(that.array, usage, depend, extra);
		auto index = generateJs(that.index, usage, depend, extra);
		return new JsObject([Tuple!(string, JsExpr)("type", new JsLit("'tuple'")),
				Tuple!(string, JsExpr)("pointer", tuplePointer), Tuple!(string,
					JsExpr)("index", index), //todo use indexTuple for indexing
				Tuple!(string, JsExpr)("get", new JsFuncLit([],
					[new JsReturn(new JsIndex(getPointer(dotThis("pointer")), dotThis("index")))])),
				Tuple!(string, JsExpr)("set",
					new JsFuncLit(["value"], [new JsBinary!"="(new JsIndex(getPointer(dotThis("pointer")),
					dotThis("index")), new JsLit("value"))]))]);
	}
}

JsExpr generateJsAddressOfImpl(Prefix!"*" that, Usage usage, JsScope depend, Extra* extra) {
	return generateJs(that.value, usage, depend, extra);
}

JsExpr generateJsImpl(Scope that, Usage usage, JsScope depend, Extra* extra) {
	return generateJsScopeImpl!((last, depend, extra) => generateJs(last, usage, depend, extra))(that,
			depend, extra);
}

void generateJsEffectsOnlyImpl(Scope that, JsScope depend, Extra* extra) {
	return generateJsScopeImpl!generateJsEffectsOnly(that, depend, extra);
}

auto generateJsScopeImpl(alias Return)(Scope that, JsScope depend, Extra* extra) {
	foreach (state; that.states) {
		if (auto value = state.castTo!Expression) {
			generateJsEffectsOnly(value, depend, extra);
		} else if (auto assign = state.castTo!Assign) {
			depend ~= generateJsAssign(assign.left, assign.right, depend, extra);
		} else if (auto vardef = state.castTo!ScopeVarDef) {
			generateJsIntoVar(vardef.definition, new JsLit(vardef.name), true,
					Case.copyObject, depend, extra);
			extra.context.variableScopes[vardef] = depend;
		} else {
			assert(0);
		}
	}
	return Return(that.last, depend, extra);
}

JsExpr generateJsAssign(Expression leftValue, Expression rightValue, JsScope depend, Extra* extra) {
	auto right = generateJs(rightValue, Usage(true), depend, extra);

	if (auto pointer = cast(Prefix!"*") leftValue) {
		auto output = generateJs(pointer.value, Usage(true), depend, extra);
		return setPointer(output, right);
	} else {
		auto output = generateJs(leftValue, Usage(true, Case.copyObject), depend, extra);
		return new JsBinary!"="(output, right);
	}
}

JsExpr generateJsImpl(FuncLit that, Usage usage, JsScope depend, Extra* extra) {
	return new JsLit(that.name);
}

JsExpr generateJsImpl(string op)(Binary!op that, Usage usage, JsScope depend, Extra* extra)
		if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = generateJs(that.left, usage, depend, extra);
	auto right = generateJs(that.right, usage, depend, extra);
	return castInt(new JsBinary!op(left, right), that.type);
}

JsExpr generateJsImpl(string op)(Binary!op that, Usage usage, JsScope depend, Extra* extra)
		if (["<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
	auto left = generateJs(that.left, usage, depend, extra);
	auto right = generateJs(that.right, usage, depend, extra);
	return new JsBinary!op(left, right);
}

JsExpr generateJsImpl(string op)(Prefix!op that, Usage usage, JsScope depend, Extra* extra)
		if (["-", "!"].canFind(op)) {
	return new JsPrefix!op(generateJs(that.value, usage, depend, extra));
}

JsExpr generateJsImpl(ExternJs that, Usage usage, JsScope depend, Extra* extra) {
	return new JsLit(that.name);
}
