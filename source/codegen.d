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

import std.algorithm;
import std.array;
import std.bigint;
import std.conv;
import std.meta;
import std.range;
import std.stdio;
import std.string;
import std.typecons;
import std.utf;
import std.variant;

import semantic.ast;
import jsast;

import misc;

//structs are repesented as native arrays
//struct are copied on caller side and on return

//arrays are either a native array or an object with a data, start, length 
// where data may have a pointer array indexed with data.{{num}}_ptr
//pointers objects with get,and set
//functions are native js functions

JsModule generateJsModule(Module mod) {
	JsModule result = new JsModule();
	auto extra = new Extra;
	foreach (symbol; mod.exports) {
		result ~= new JsVarDef(symbol.name, symbol.generateSymbol(result, extra));
	}
	applyGlobalRequests(result, extra);
	return result;
}

void applyGlobalRequests(JsScope depend, Extra* extra) {
	void applyRequest(ref Type[] array, JsFuncLit function(Expression,
			Extra*) create, string prefix) {
		while (array.length) {
			depend ~= new JsVarDef(prefix ~ array[$ - 1].mangle, create(array[$ - 1], extra));
			array.popBack;
		}
	}

	applyRequest(extra.copyFunctions, &createCopy, "__copy_");
	applyRequest(extra.compareFunctions, &createCompare, "__compare_");
}

JsExpr generateSymbolImpl(ModuleVarDef that, JsScope depend, Extra* extra) {
	extra.context = FunctionContext();
	return that.value.generateJs(Usage(true, Case.copyObject), depend, extra);
}

JsExpr generateSymbolImpl(FunctionLiteral that, JsScope depend, Extra* extra) {
	extra.context = FunctionContext();
	extra.context.argumentName = genName(extra);
	auto result = new JsFuncLit([extra.context.argumentName], []);
	if (!sameType(that.text.type, new TypeStruct())) {
		auto val = that.text.generateJs(Usage(true, Case.copyObject), result.states, extra);
		result.states ~= new JsReturn(val);
	} else {
		that.text.generateJsEffectsOnly(result.states, extra);
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
	JsLit[ScopeVar] localPointers;
	JsScope[ScopeVar] variableScopes;

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

JsExpr indexPointerArray(JsExpr array, JsExpr index) {
	return new JsIndex(internalArray(array),
			new JsBinary!"+"(new JsBinary!"+"(arrayStart(array), index), new JsLit("\"_ptr\"")));
}

JsExpr getPointer(JsExpr pointer) {
	return new JsCall(new JsDot(pointer, "get"), []);
}

JsExpr setPointer(JsExpr pointer, JsExpr value) {
	return new JsCall(new JsDot(pointer, "set"), [value]);
}

JsExpr createArrayPointer(JsExpr array, JsExpr index) {
	return new JsObject([
			Tuple!(string, JsExpr)("array", array),
			Tuple!(string, JsExpr)("get", new JsFuncLit([],
				[
					new JsReturn(indexArray(new JsDot(new JsLit("this"), "array"), index))
				])),
			Tuple!(string, JsExpr)("set", new JsFuncLit(["value"],
				[
					new JsBinary!"="(indexArray(new JsDot(new JsLit("this"),
					"array"), index), new JsLit("value"))
				]))
			]);
}

JsExpr createLocalPointer(JsExpr variable) {
	return new JsObject([
			Tuple!(string, JsExpr)("get", new JsFuncLit([],
				[new JsReturn(variable)])),
			Tuple!(string, JsExpr)("set", new JsFuncLit(["value"],
				[new JsBinary!"="(variable, new JsLit("value"))]))
			]);
}

JsExpr copy(JsExpr expr, Expression type, Extra* extra) {
	return dispatch!(copyImpl, TypeBool, TypeChar, TypeInt, TypeStruct,
			TypePointer, TypeArray, TypeFunction)(type, expr, extra);
}

JsExpr copyImpl(T)(T, JsExpr expr, Extra*)
		if (staticIndexOf!(T, TypeBool, TypeChar, TypeInt, TypePointer,
			TypeArray, TypeFunction) >= 0) {
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
	return new JsCall(new JsLit("__copy_" ~ that.mangle), [expr]);
}

JsFuncLit createCopy(Expression type, Extra* extra) {
	assert(type.castTo!(TypeStruct));
	auto typeStruct = type.castTo!(TypeStruct);
	auto argumentName = genName(extra);
	return new JsFuncLit([argumentName],
			[
				new JsReturn(new JsArray(typeStruct.values.enumerate.map!(
					a => copy(indexTuple(new JsLit(argumentName), a[0]), a[1], extra)).array))
			]);
}

JsExpr defaultValue(Expression type) {
	return dispatch!(defaultValueImpl, TypeBool, TypeChar, TypeInt,
			TypePointer, TypeArray, TypeFunction, TypeStruct)(type);
}

JsExpr defaultValueImpl(T)(T that) {
	static if (is(T == TypeBool)) {
		return new JsLit("false");
	} else static if (is(T == TypeInt)) {
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
		if (i.signed) {
			if (i.size == 8) {
				assert(0, "todo support size" ~ i.size.to!string);
			} else if (i.size == 16) {
				assert(0, "todo support size" ~ i.size.to!string);
			} else if (i.size == 32 || i.size == 0) {
				return new JsBinary!"|"(expr, new JsLit("0"));
			} else {
				assert(0, "todo support size" ~ i.size.to!string);
			}
		} else {
			if (i.size == 8) {
				return new JsBinary!"&"(expr, new JsLit("0xff"));
			} else if (i.size == 16) {
				return new JsBinary!"&"(expr, new JsLit("0xffff"));
			} else if (i.size == 32 || i.size == 0) {
				return new JsBinary!"&"(expr, new JsLit("0xffffffff"));
			} else {
				assert(0, "todo support size" ~ i.size.to!string);
			}
		}
	} else {
		assert(0);
	}
}

JsExpr compare(JsExpr left, JsExpr right, Expression type, Extra* extra) {
	return dispatch!(compareImpl, TypeBool, TypeChar, TypeInt, TypeFunction,
			TypePointer, TypeArray, TypeStruct)(type, left, right, extra);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, Extra* extra)
		if (staticIndexOf!(T, TypeBool, TypeChar, TypeInt, TypeFunction, TypePointer) >= 0) {
	return new JsBinary!"=="(left, right);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, Extra* extra)
		if (staticIndexOf!(T, TypeArray, TypeStruct) >= 0) {
	auto range = extra.compareFunctions.find!sameType(that);
	if (range.empty) {
		extra.compareFunctions ~= that;
	}
	return new JsCall(new JsLit("__compare_" ~ that.mangle), [left, right]);
}

JsFuncLit createCompare(Expression that, Extra* extra) {
	auto Function = new JsFuncLit(["left", "right"], []);
	dispatch!(createCompareImpl, TypeArray, TypeStruct)(that, new JsLit("left"),
			new JsLit("right"), Function.states, extra);
	return Function;
}

void createCompareImpl(TypeArray that, JsExpr left, JsExpr right, JsScope depend, Extra* extra) {
	auto lengthCompare = new JsBinary!"!="(arrayLength(left), arrayLength(right));
	depend.states ~= new JsIf(lengthCompare, [new JsReturn(new JsLit("false"))], [
			]);

	auto iterator = new JsLit(genName(extra));
	auto For = new JsFor(new JsVarDef(iterator.value, new JsLit("0")),
			new JsBinary!"<"(iterator, arrayLength(left)), new JsPostfix!"++"(iterator), [
			]);
	depend ~= For;

	auto elementComparer = new JsPrefix!"!"(compare(indexArray(left, iterator),
			indexArray(right, iterator), that.array, extra));

	For.states ~= new JsIf(elementComparer, [new JsReturn(new JsLit("false"))], [
			]);

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

JsState assignTo(bool createVar, JsLit left, JsExpr right) {
	if (createVar) {
		return new JsVarDef(left.value, right);
	} else {
		return new JsBinary!"="(left, right);
	}
}

JsExpr generateJsImpl(IntLit that, Usage usage, JsScope depend, Extra* extra) {
	return new JsLit(that.value.to!string);
}

JsExpr generateJsImpl(ExternJs that, Usage usage, JsScope depend, Extra* extra) {
	return new JsLit(that.name);
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
	depend ~= assignTo(createVar, variable, that.generateJs(Usage(true,
			shouldCopy), depend, extra));
}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra* extra)
		if (staticIndexOf!(T, BoolLit, CharLit, ScopeVarClass!true, ModuleVarRef,
			FuncArgument, StringLit, IntLit, ExternJs, FunctionLiteral) >= 0) {

}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra* extra)
		if (staticIndexOf!(T, New, CastInteger, Length, Prefix!"-", Deref,
			Address, Prefix!"!") >= 0) {
	that.value.generateJsEffectsOnly(depend, extra);
}

void generateJsEffectsOnlyImpl(string op)(Binary!op that, JsScope depend, Extra* extra) {
	that.left.generateJsEffectsOnly(depend, extra);
	that.right.generateJsEffectsOnly(depend, extra);
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
	return new JsArray(that.values.map!(a => a.generateJs(usage, depend, extra)).array);
}

void generateJsEffectsOnlyImpl(TupleLit that, JsScope depend, Extra* extra) {
	that.values.each!(a => a.generateJsEffectsOnly(depend, extra));
}

JsExpr generateJsImpl(ModuleVarRef that, Usage usage, JsScope depend, Extra* extra) {
	return maybeCopy(new JsLit(that.definition.name), that.type, usage, extra);
}

JsExpr generateJsImpl(ScopeVarClass!true that, Usage usage, JsScope depend, Extra* extra) {
	return maybeCopy(new JsLit(that.name), that.type, usage, extra);
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
	If.cond = that.cond.generateJs(Usage(true), depend, extra);
	that.yes.generateJsIntoVar(variable, false, shouldCopy, If.yes, extra);
	that.no.generateJsIntoVar(variable, false, shouldCopy, If.no, extra);
	depend ~= If;
}

void generateJsEffectsOnlyImpl(If that, JsScope depend, Extra* extra) {
	auto If = new JsIf();
	If.cond = that.cond.generateJs(Usage(true), depend, extra);
	that.yes.generateJsEffectsOnly(If.yes, extra);
	that.no.generateJsEffectsOnly(If.no, extra);
	depend ~= If;
}

JsExpr generateJsImpl(While that, Usage usage, JsScope depend, Extra* extra) {
	auto While = new JsWhile();
	auto cond = that.cond.generateJs(Usage(true), While.states, extra);

	if (While.states.length == 0) {
		While.cond = cond;
		that.state.generateJsEffectsOnly(While.states, extra);
	} else {
		While.cond = new JsLit("true");
		While.states ~= new JsIf(new JsPrefix!"!"(cond), [new JsBreak()], []);
		that.state.generateJsEffectsOnly(While.states, extra);
	}
	depend ~= While;
	return new JsArray([]);
}

void generateJsEffectsOnlyImpl(While that, JsScope depend, Extra* extra) {
	generateJsImpl(that, Usage(), depend, extra);
}

JsExpr generateJsImpl(New that, Usage usage, JsScope depend, Extra* extra) {
	auto local = new JsLit(genName(extra));
	that.value.generateJsIntoVar(local, true, Case.copyObject, depend, extra);
	if (usage.sideEffects) {
		return createLocalPointer(local);
	} else {
		return createVarAndGenerateInto(that, Usage(true), depend, extra);
	}
}

void generateJsIntoVarImpl(NewArray that, JsLit variable, bool createVar,
		Case shouldCopy, JsScope depend, Extra* extra) {
	auto length = that.length.generateJs(Usage(false), depend, extra);
	auto expression = that.value.generateJs(Usage(false, Case.copyObject), depend, extra);

	depend ~= assignTo(createVar, variable, new JsArray());
	auto iterator = new JsLit(genName(extra));
	depend ~= new JsFor(new JsVarDef(iterator.value, new JsLit("0")),
			new JsBinary!"<"(iterator, length), new JsPostfix!"++"(iterator),
			[new JsBinary!"="(new JsIndex(variable, iterator), expression)]);
}

void generateJsEffectsOnlyImpl(NewArray that, JsScope depend, Extra* extra) {
	that.value.generateJsEffectsOnly(depend, extra);
	that.length.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(CastInteger that, Usage usage, JsScope depend, Extra* extra) {
	auto value = that.value.generateJs(usage, depend, extra);
	return castInt(value, that.type);
}

JsExpr generateJsImpl(Length that, Usage usage, JsScope depend, Extra* extra) {
	auto value = that.value.generateJs(usage, depend, extra);
	return arrayLength(value);
}

JsExpr generateJsImpl(Index that, Usage usage, JsScope depend, Extra* extra) {
	auto array = that.array.generateJs(Usage(false), depend, extra);
	auto index = that.index.generateJs(Usage(false), depend, extra);
	return indexArray(array, index);
}

JsExpr generateJsImpl(bool lvalue)(TupleIndex!lvalue that, Usage usage,
		JsScope depend, Extra* extra) {
	auto tuple = that.tuple.generateJs(usage, depend, extra);
	return indexTuple(tuple, that.index);
}

void generateJsEffectsOnlyImpl(Index that, JsScope depend, Extra* extra) {
	that.array.generateJsEffectsOnly(depend, extra);
	that.index.generateJsEffectsOnly(depend, extra);
}

void generateJsEffectsOnlyImpl(bool lvalue)(TupleIndex!lvalue that, JsScope depend, Extra* extra) {
	that.tuple.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(Call that, Usage usage, JsScope depend, Extra* extra) {
	if (usage.sideEffects) {
		auto functionPointer = that.calle.generateJs(Usage(true), depend, extra);
		auto argument = that.argument.generateJs(Usage(true, Case.copyObject), depend, extra);
		auto expression = new JsCall(functionPointer, [argument]);
		return expression;
	} else {
		return createVarAndGenerateInto(that, Usage(true, Case.copyObject), depend, extra);
	}
}

void generateJsEffectsOnlyImpl(Call that, JsScope depend, Extra* extra) {
	auto functionPointer = that.calle.generateJs(Usage(true), depend, extra);
	auto argument = that.argument.generateJs(Usage(true, Case.copyObject), depend, extra);
	depend ~= new JsCall(functionPointer, [argument]);
}

JsExpr generateJsImpl(Slice that, Usage usage, JsScope depend, Extra* extra) {
	auto array = that.array.generateJs(Usage(false), depend, extra);
	auto left = that.left.generateJs(Usage(false), depend, extra);
	auto right = that.right.generateJs(Usage(false), depend, extra);
	return new JsObject([
			Tuple!(string, JsExpr)("data", internalArray(array)),
			Tuple!(string, JsExpr)("start", new JsBinary!"+"(arrayStart(array),
				left)),
			Tuple!(string, JsExpr)("length", new JsBinary!"-"(right, left))
			]);
}

void generateJsEffectsOnlyImpl(Slice that, JsScope depend, Extra* extra) {
	that.array.generateJsEffectsOnly(depend, extra);
	that.left.generateJsEffectsOnly(depend, extra);
	that.right.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(StringLit that, Usage usage, JsScope depend, Extra* extra) {
	return new JsArray(that.value
			.map!(a => new JsLit('"' ~ [a].to!string ~ '"'))
			.map!(a => a.convert!JsExpr)
			.array);
}

JsExpr generateJsImpl(ArrayLit that, Usage usage, JsScope depend, Extra* extra) {
	if (usage.sideEffects) {
		return new JsArray(that.values.map!(a => a.generateJs(Usage(true,
				Case.copyObject), depend, extra)).array);
	} else {
		return createVarAndGenerateInto(that, Usage(false), depend, extra);
	}
}

void generateJsEffectsOnlyImpl(ArrayLit that, JsScope depend, Extra* extra) {
	that.values.each!(a => a.generateJsEffectsOnly(depend, extra));
}

JsExpr generateJsImpl(Binary!"==" that, Usage usage, JsScope depend, Extra* extra) {
	auto left = that.left.generateJs(Usage(usage.sideEffects, Case.accessField), depend, extra);
	auto right = that.right.generateJs(Usage(usage.sideEffects, Case.accessField), depend, extra);
	return compare(left, right, that.left.type, extra);
}

JsExpr generateJsImpl(Binary!"!=" that, Usage usage, JsScope depend, Extra* extra) {
	auto left = that.left.generateJs(Usage(usage.sideEffects, Case.accessField), depend, extra);
	auto right = that.right.generateJs(Usage(usage.sideEffects, Case.accessField), depend, extra);
	return new JsPrefix!"!"(compare(left, right, that.left.type, extra));
}

JsExpr generateJsImpl(Binary!"~" that, Usage usage, JsScope depend, Extra* extra) {
	assert(0, "todo implement ~");
}

JsExpr generateJsImpl(Deref that, Usage usage, JsScope depend, Extra* extra) {
	return getPointer(that.value.generateJs(usage, depend, extra));
}

JsExpr generateJsImpl(Address that, Usage usage, JsScope depend, Extra* extra) {
	return that.value.generateJsAddressOf(usage, depend, extra);
}

JsExpr generateJsAddressOfImpl(ScopeVarClass!true that0, Usage usage, JsScope depend, Extra* extra) {
	auto that = that0.convert!ScopeVar;
	if (that in extra.context.localPointers) {
		return extra.context.localPointers[that];
	}
	auto pointer = new JsLit(genName(extra));
	extra.context.variableScopes[that] ~= new JsVarDef(pointer.value,
			createLocalPointer(new JsLit(that.name)));
	extra.context.localPointers[that] = pointer;
	return pointer;
}

JsExpr generateJsAddressOfImpl(ModuleVarRef that, Usage usage, JsScope depend, Extra* extra) {
	assert(0, "todo implement module pointers");
}

JsExpr generateJsAddressOfImpl(Index that, Usage usage, JsScope depend, Extra* extra) {
	auto array = that.array.generateJs(Usage(false), depend, extra);
	auto index = that.index.generateJs(Usage(false), depend, extra);
	depend ~= new JsBinary!"="(indexPointerArray(array, index),
			new JsBinary!"||"(indexPointerArray(array, index), createArrayPointer(array, index)));
	return indexPointerArray(array, index);
}

JsExpr generateJsAddressOfImpl(TupleIndex!true that, Usage usage, JsScope depend, Extra* extra) {
	auto structType = that.tuple.type.castTo!(TypeStruct);
	auto tuplePointer = that.tuple.generateJsAddressOf(usage, depend, extra);
	auto index = that.index;
	assert(0, "todo support pointers to tuples");
}

JsExpr generateJsAddressOfImpl(Deref that, Usage usage, JsScope depend, Extra* extra) {
	return that.value.generateJs(usage, depend, extra);
}

JsExpr generateJsImpl(Scope that, Usage usage, JsScope depend, Extra* extra) {
	that.pass.generateJsEffectsOnly(depend, extra);
	return that.last.generateJs(usage, depend, extra);
}

void generateJsEffectsOnlyImpl(Scope that, JsScope depend, Extra* extra) {
	that.pass.generateJsEffectsOnly(depend, extra);
	that.last.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(ScopeVarDef that, Usage usage, JsScope depend, Extra* extra) {
	that.variable.value.generateJsIntoVar(new JsLit(that.variable.name), true,
			Case.copyObject, depend, extra);
	extra.context.variableScopes[that.variable] = depend;
	return that.last.generateJs(usage, depend, extra);
}

void generateJsEffectsOnlyImpl(ScopeVarDef that, JsScope depend, Extra* extra) {
	that.variable.value.generateJsIntoVar(new JsLit(that.variable.name), true,
			Case.copyObject, depend, extra);
	extra.context.variableScopes[that.variable] = depend;
	that.last.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(Assign that, Usage usage, JsScope depend, Extra* extra) {
	depend ~= generateJsAssign(that.left, that.right, depend, extra);
	return that.last.generateJs(usage, depend, extra);
}

void generateJsEffectsOnlyImpl(Assign that, JsScope depend, Extra* extra) {
	depend ~= generateJsAssign(that.left, that.right, depend, extra);
	that.last.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsAssign(LValueExpression leftValue, RuntimeExpression rightValue,
		JsScope depend, Extra* extra) {
	auto right = rightValue.generateJs(Usage(true), depend, extra);

	if (auto pointer = cast(Deref) leftValue) {
		auto output = pointer.value.generateJs(Usage(true), depend, extra);
		return setPointer(output, right);
	} else {
		auto output = leftValue.generateJs(Usage(true, Case.copyObject), depend, extra);
		return new JsBinary!"="(output, right);
	}
}

JsExpr generateJsImpl(FunctionLiteral that, Usage usage, JsScope depend, Extra* extra) {
	return new JsLit(that.name);
}

JsExpr generateJsImpl(string op)(Binary!op that, Usage usage, JsScope depend, Extra* extra)
		if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = that.left.generateJs(usage, depend, extra);
	auto right = that.right.generateJs(usage, depend, extra);
	return castInt(new JsBinary!op(left, right), that.type);
}

JsExpr generateJsImpl(string op)(Binary!op that, Usage usage, JsScope depend, Extra* extra)
		if (["<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
	auto left = that.left.generateJs(usage, depend, extra);
	auto right = that.right.generateJs(usage, depend, extra);
	return new JsBinary!op(left, right);
}

JsExpr generateJsImpl(string op)(Prefix!op that, Usage usage, JsScope depend, Extra* extra)
		if (["-", "!"].canFind(op)) {
	return new JsPrefix!op(that.value.generateJs(usage, depend, extra));
}
