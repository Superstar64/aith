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

import std.algorithm : canFind, each, find, filter, joiner, map;
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

import semanticast;
import jsast;

import misc;

//structs are repesented as native arrays
//struct are copied on caller side and on return

//arrays are either a native array or an object with a data, start, length
//pointers objects with type,get,and set
//the pointer types are 'local,'array' and 'tuple'
//functions are native js functions

JsModule generateJsModule(Module mod) {
	JsModule result = new JsModule();
	auto extra = new Extra;
	foreach (symbol; mod.exports) {
		result ~= new JsVarDef(symbol.name, dispatch!(generateSymbol,
				ModuleVarDef, FuncLit)(symbol, result, extra));
	}
	applyGlobalRequests(result, extra);
	return result;
}

void applyGlobalRequests(JsScope depend, Extra* extra) {
	void applyRequest(ref Type[] array, JsFuncLit function(Expression,
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
	return generateJs(that.value, Usage(true, Case.copyObject), depend, extra);
}

JsExpr generateSymbol(FuncLit that, JsScope depend, Extra* extra) {
	extra.context = FunctionContext();
	extra.context.argumentName = genName(extra);
	auto result = new JsFuncLit([extra.context.argumentName], []);
	if (!sameType(that.text.type, new TypeStruct())) {
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
	Type[] copyFunctions;

	Type[] compareFunctions;
}

JsExpr symbolName(T)(T var, Extra* extra) {
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
	return dispatch!(mangleImpl, TypeBool, TypeChar, TypeInt, TypeUInt,
			TypeStruct, TypePointer, TypeArray, TypeFunction)(type);
}

string mangleImpl(TypeBool type) {
	return "bool";
}

string mangleImpl(TypeChar type) {
	return "char";
}

string mangleImpl(TypeInt type) {
	return "int" ~ type.size.to!string;
}

string mangleImpl(TypeUInt type) {
	return "uint" ~ type.size.to!string;
}

string mangleImpl(TypeStruct type) {
	return "struct$" ~ type.values.map!mangle.map!(a => a ~ "_").joiner.array.to!string ~ "$";
}

string mangleImpl(TypePointer type) {
	return type.value.mangle ~ "_pointer";
}

string mangleImpl(TypeArray type) {
	return type.array.mangle ~ "_array";
}

string mangleImpl(TypeFunction type) {
	return "function$" ~ type.calle.mangle ~ "$" ~ type.argument.mangle ~ "$";
}

JsExpr copy(JsExpr expr, Expression type, Extra* extra) {
	return dispatch!(copyImpl, TypeBool, TypeChar, TypeInt, TypeUInt,
			TypeStruct, TypePointer, TypeArray, TypeFunction)(type, expr, extra);
}

JsExpr copyImpl(T)(T, JsExpr expr, Extra*)
		if (staticIndexOf!(T, TypeBool, TypeChar, TypeInt, TypeUInt,
			TypePointer, TypeArray, TypeFunction) >= 0) {
	return expr;
}

JsExpr copyImpl(TypeStruct that, JsExpr expr, Extra* extra) {
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
	assert(type.castTo!TypeStruct);
	auto TypeStruct = type.castTo!TypeStruct;
	auto argumentName = genName(extra);
	return new JsFuncLit([argumentName],
			[new JsReturn(new JsArray(TypeStruct.values.enumerate.map!(
				a => copy(indexTuple(new JsLit(argumentName), a[0]), a[1], extra)).array))]);
}

JsExpr defaultValue(Expression type) {
	return dispatch!(defaultValueImpl, TypeBool, TypeChar, TypeInt, TypeUInt,
			TypePointer, TypeArray, TypeFunction, TypeStruct)(type);
}

JsExpr defaultValueImpl(T)(T that) {
	static if (is(T == TypeBool)) {
		return new JsLit("false");
	} else static if (is(T == TypeUInt) || is(T == TypeInt)) {
		return new JsLit("0");
	} else static if (is(T == TypeChar)) {
		return new JsLit('"' ~ "\\0" ~ '"');
	} else static if (is(T == TypeStruct)) {
		auto ret = new JsArray();
		foreach (subType; that.values) {
			ret.exprs ~= defaultValue(subType);
		}
		return ret;
	} else static if (is(T == TypePointer) || is(T == TypeArray)) {
		return new JsLit("undefined");
	} else static if (is(T == TypeFunction)) {
		return new JsArray();
	} else {
		static assert(0);
	}
}

JsExpr castInt(JsExpr expr, Expression type) {
	type = type;
	if (auto i = type.castTo!TypeInt) {
		if (i.size == 1) {
			assert(0, "todo support size" ~ i.size.to!string);
		} else if (i.size == 2) {
			assert(0, "todo support size" ~ i.size.to!string);
		} else if (i.size == 4 || i.size == 0) {
			return new JsBinary!"|"(expr, new JsLit("0"));
		} else {
			assert(0, "todo support size" ~ i.size.to!string);
		}
	} else if (auto i = type.castTo!TypeUInt) {
		if (i.size == 1) {
			return new JsBinary!"&"(expr, new JsLit("0xff"));
		} else if (i.size == 2) {
			return new JsBinary!"&"(expr, new JsLit("0xffff"));
		} else if (i.size == 4 || i.size == 0) {
			return new JsBinary!"&"(expr, new JsLit("0xffffffff"));
		} else {
			assert(0, "todo support size" ~ i.size.to!string);
		}
	} else {
		assert(0);
	}
}

JsExpr compare(JsExpr left, JsExpr right, Expression type, Extra* extra) {
	return dispatch!(compareImpl, TypeBool, TypeChar, TypeInt, TypeUInt,
			TypeFunction, TypePointer, TypeArray, TypeStruct)(type, left, right, extra);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, Extra* extra)
		if (staticIndexOf!(T, TypeBool, TypeChar, TypeInt, TypeUInt, TypeFunction) >= 0) {
	return new JsBinary!"=="(left, right);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, Extra* extra)
		if (staticIndexOf!(T, TypePointer, TypeArray, TypeStruct) >= 0) {
	auto range = extra.compareFunctions.find!sameType(that);
	if (range.empty) {
		extra.compareFunctions ~= that;
	}
	return new JsCall(new JsLit("__compare_" ~ mangle(that)), [left, right]);
}

JsFuncLit createCompare(Expression that, Extra* extra) {
	auto Function = new JsFuncLit(["left", "right"], []);
	dispatch!(createCompareImpl, TypePointer, TypeArray, TypeStruct)(that,
			new JsLit("left"), new JsLit("right"), Function.states, extra);
	return Function;
}

void createCompareImpl(TypePointer that, JsExpr left, JsExpr right, JsScope depend, Extra* extra) {
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

void createCompareImpl(TypeArray that, JsExpr left, JsExpr right, JsScope depend, Extra* extra) {
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

void createCompareImpl(TypeStruct that, JsExpr left, JsExpr right, JsScope depend, Extra* extra) {
	if (that.values.length == 0) {
		depend ~= new JsReturn(new JsLit("true"));
	}
	depend ~= new JsReturn(createCompareImplStruct(0, that, left, right, depend, extra));
}

JsExpr createCompareImplStruct(uint index, TypeStruct that, JsExpr left,
		JsExpr right, JsScope depend, Extra* extra) {
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
		FuncArgument, If, While, New, NewArray, CastInteger, Length, Index,
		TupleIndex, Call, Slice, StringLit, ArrayLit, Binary!"==",
		Binary!"!=", Binary!"~", Prefix!"*", Prefix!"&", Scope, FuncLit,
		Binary!"*", Binary!"/", Binary!"%", Binary!"+", Binary!"-",
		Binary!"<=", Binary!">=", Binary!"<", Binary!">", Binary!"&&",
		Binary!"||", Prefix!"-", Prefix!"!", CastExtern);

JsExpr generateJs(Expression that, Usage usage, JsScope depend, Extra* extra) {
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
	return dispatch!(generateJsIntoVarImpl, Nodes)(that, variable, createVar,
			shouldCopy, depend, extra);
}

//todo print warning if unusal node(new,intlit,etc)
void generateJsEffectsOnly(Expression that, JsScope depend, Extra* extra) {
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
			ModuleVarRef, FuncArgument, StringLit, FuncLit, CastExtern) >= 0) {

}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra* extra)
		if (staticIndexOf!(T, New, CastInteger, Length, Prefix!"+",
			Prefix!"-", Prefix!"*", Prefix!"/", Prefix!"&", Prefix!"!") >= 0) {
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

JsExpr generateJsImpl(CastInteger that, Usage usage, JsScope depend, Extra* extra) {
	auto value = generateJs(that.value, usage, depend, extra);
	return castInt(value, that.wanted);
}

JsExpr generateJsImpl(Length that, Usage usage, JsScope depend, Extra* extra) {
	auto value = generateJs(that.value, usage, depend, extra);
	return arrayLength(value);
}

JsExpr generateJsImpl(Index that, Usage usage, JsScope depend, Extra* extra) {
	auto array = generateJs(that.array, Usage(false), depend, extra);
	auto index = generateJs(that.index, Usage(false), depend, extra);
	return indexArray(array, index);
}

JsExpr generateJsImpl(TupleIndex that, Usage usage, JsScope depend, Extra* extra) {
	auto tuple = generateJs(that.tuple, usage, depend, extra);
	return indexTuple(tuple, that.index);
}

void generateJsEffectsOnlyImpl(Index that, JsScope depend, Extra* extra) {
	generateJsEffectsOnly(that.array, depend, extra);
	generateJsEffectsOnly(that.index, depend, extra);
}

void generateJsEffectsOnlyImpl(TupleIndex that, JsScope depend, Extra* extra) {
	generateJsEffectsOnly(that.tuple, depend, extra);
}

JsExpr generateJsImpl(Call that, Usage usage, JsScope depend, Extra* extra) {
	if (usage.sideEffects) {
		auto functionPointer = generateJs(that.calle, Usage(true), depend, extra);
		auto argument = generateJs(that.argument, Usage(true, Case.copyObject), depend, extra);
		auto expression = new JsCall(functionPointer, [argument]);
		return expression;
	} else {
		return createVarAndGenerateInto(that, Usage(true, Case.copyObject), depend, extra);
	}
}

void generateJsEffectsOnlyImpl(Call that, JsScope depend, Extra* extra) {
	auto functionPointer = generateJs(that.calle, Usage(true), depend, extra);
	auto argument = generateJs(that.argument, Usage(true, Case.copyObject), depend, extra);
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
	return new JsArray(that.value.map!(a => new JsLit('"' ~ [a].to!string ~ '"'))
			.map!(a => a.castTo!JsExpr).array);
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
	return dispatch!(generateJsAddressOfImpl, ScopeVarRef, ModuleVarRef,
			TupleIndex, Index, Prefix!"*")(that.value, usage, depend, extra);
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

JsExpr generateJsAddressOfImpl(Index that, Usage usage, JsScope depend, Extra* extra) {
	enum dotThis = (string expression) => new JsDot(new JsLit("this"), expression);
	auto array = generateJs(that.array, usage, depend, extra);
	auto index = generateJs(that.index, usage, depend, extra);

	return new JsObject([Tuple!(string, JsExpr)("type", new JsLit("'array'")),
			Tuple!(string, JsExpr)("array", array), Tuple!(string, JsExpr)("index",
				index), Tuple!(string, JsExpr)("get", new JsFuncLit([],
				[new JsReturn(indexArray(dotThis("array"), dotThis("index")))])), Tuple!(string, JsExpr)("set",
				new JsFuncLit(["value"], [new JsBinary!"="(indexArray(dotThis("array"),
				dotThis("index")), new JsLit("value"))]))]);
}

JsExpr generateJsAddressOfImpl(TupleIndex that, Usage usage, JsScope depend, Extra* extra) {
	enum dotThis = (string expression) => new JsDot(new JsLit("this"), expression);
	auto structType = that.tuple.type.castTo!TypeStruct;
	auto tuplePointer = dispatch!(generateJsAddressOfImpl, ScopeVarRef,
			ModuleVarRef, Index, Prefix!"*")(that.tuple, usage, depend, extra);
	auto index = that.index;
	return new JsObject([Tuple!(string, JsExpr)("type", new JsLit("'tuple'")),
			Tuple!(string, JsExpr)("pointer", tuplePointer), Tuple!(string,
				JsExpr)("index", new JsLit(index.to!string)), Tuple!(string, JsExpr)("get",
				new JsFuncLit([], [new JsReturn(new JsIndex(getPointer(dotThis("pointer")),
				dotThis("index")))])), Tuple!(string, JsExpr)("set", new JsFuncLit(["value"],
				[new JsBinary!"="(new JsIndex(getPointer(dotThis("pointer")),
				dotThis("index")), new JsLit("value"))]))]);
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
			generateJsIntoVar(vardef.value, new JsLit(vardef.name), true,
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

JsExpr generateJsImpl(CastExtern that, Usage usage, JsScope depend, Extra* extra) {
	return new JsLit(that.value.name);
}
