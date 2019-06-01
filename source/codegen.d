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
	Symbol[string] symbols = mod.exports.dup;
	foreach (literal; mod.functionSpecializations.byValue.map!(a => a.byValue).joiner) {
		assert(!(literal.name in symbols));
		symbols[literal.name] = literal;
	}
	foreach (symbol; symbols) {
		extra.symbols[symbol] = new JsVariable(defaultNaming(symbol.name));
	}

	foreach (symbol; symbols) {
		result ~= new JsVarDef(extra.symbols[symbol], symbol.generateSymbol(result, extra));
	}
	applyGlobalRequests(result, extra);
	return result;
}

void applyGlobalRequests(JsScope depend, Extra extra) {
	while (extra.compareSymbols.length) {
		auto type = extra.compareSymbols.byKey.front;
		auto variable = extra.compareSymbols[type];

		depend ~= new JsVarDef(variable, createCompare(type, extra));

		extra.compareSymbols.remove(type);
	}
}

JsExpr generateSymbolImpl(ModuleVarDef that, JsScope depend, Extra extra) {
	extra.context = FunctionContext();
	return that.value.generateJs(Usage(true), depend, extra);
}

JsExpr generateSymbolImpl(FunctionLiteral that, JsScope depend, Extra extra) {
	extra.context = FunctionContext();
	extra.context.argument = new JsVariable(temporary);
	auto result = new JsFuncLit([extra.context.argument], []);
	if (!sameType(that.text.type, new TypeStruct())) {
		auto val = that.text.generateJs(Usage(true), result.states, extra);
		result.states ~= new JsReturn(val);
	} else {
		that.text.generateJsEffectsOnly(result.states, extra);
	}

	return result;
}

struct Usage {
	//if false side effects must be dumped into it's scope
	// and the result expression must always return the same reference 
	bool sideEffects;
}

struct FunctionContext {
	JsVariable[ScopeVar] localPointers;
	JsScope[ScopeVar] variableScopes;
	JsVariable[ScopeVar] variables;

	JsVariable argument;
}

class Extra {
	FunctionContext context;

	JsVariable[Type] compareSymbols;
	JsVariable[Symbol] symbols;
}

JsExpr indexTuple(JsExpr tuple, size_t index) {
	return new JsIndex(tuple, new JsIntLit(index));
}

JsExpr indexTuplePointer(JsExpr tuple, size_t index) {
	return new JsIndex(new JsDot(tuple, "ptr"), new JsIntLit(index));
}

JsExpr createTuplePointer(Type type, JsExpr tuple, size_t index) {
	auto common = [
		Tuple!(string, JsExpr)("tuple", tuple),
		Tuple!(string, JsExpr)("get", new JsFuncLit([],
				[new JsReturn(indexTuple(new JsDot(new JsThis(), "tuple"), index))]))
	];
	if (!type.castTo!TypeStruct) {
		auto variable = new JsVariable(defaultNaming("value"));
		common ~= Tuple!(string, JsExpr)("set", new JsFuncLit([variable],
				[
					new JsBinary!"="(indexTuple(new JsDot(new JsThis(), "tuple"), index), variable)
				]));
	}
	return new JsObject(common);
}

void getOrCreateTuplePointer(Type type, JsExpr tuple, size_t index, JsScope depend) {
	depend ~= new JsBinary!"="(new JsDot(tuple, "ptr"),
			new JsBinary!"||"(new JsDot(tuple, "ptr"), new JsArray()));
	depend ~= new JsBinary!"="(indexTuplePointer(tuple, index), new JsBinary!"||"(
			indexTuplePointer(tuple, index), createTuplePointer(type, tuple, index)));
}

JsExpr internalArray(JsExpr array) {
	return new JsBinary!"||"(new JsDot(array, "data"), array);
}

JsExpr arrayStart(JsExpr array) {
	return new JsBinary!"||"(new JsDot(array, "start"), new JsIntLit(0));
}

JsExpr arrayLength(JsExpr array) {
	return new JsDot(array, "length");
}

JsExpr indexArray(JsExpr array, JsExpr index) {
	return new JsIndex(internalArray(array), new JsBinary!"+"(arrayStart(array), index));
}

JsExpr indexPointerArray(JsExpr array, JsExpr index) {
	return new JsIndex(new JsDot(internalArray(array), "ptr"),
			new JsBinary!"+"(arrayStart(array), index));
}

JsExpr createArrayPointer(Type type, JsExpr array, JsExpr index) {
	auto common = [
		Tuple!(string, JsExpr)("array", array),
		Tuple!(string, JsExpr)("get", new JsFuncLit([],
				[new JsReturn(indexArray(new JsDot(new JsThis(), "array"), index))]))
	];
	if (!type.castTo!TypeStruct) {
		auto variable = new JsVariable(defaultNaming("value"));
		common ~= Tuple!(string, JsExpr)("set", new JsFuncLit([variable],
				[
					new JsBinary!"="(indexArray(new JsDot(new JsThis(), "array"), index), variable)
				]));
	}
	return new JsObject(common);
}

void getOrCreateArrayPointer(Type type, JsExpr array, JsExpr index, JsScope depend) {
	depend ~= new JsBinary!"="(new JsDot(internalArray(array), "ptr"),
			new JsBinary!"||"(new JsDot(internalArray(array), "ptr"), new JsArray()));
	depend ~= new JsBinary!"="(indexPointerArray(array, index), new JsBinary!"||"(
			indexPointerArray(array, index), createArrayPointer(type, array, index)));
}

JsExpr getPointer(JsExpr pointer) {
	return new JsCall(new JsDot(pointer, "get"), []);
}

JsExpr setPointer(JsExpr pointer, JsExpr value) {
	return new JsCall(new JsDot(pointer, "set"), [value]);
}

JsExpr createLocalPointer(Type type, JsExpr variable) {
	auto common = [
		Tuple!(string, JsExpr)("get", new JsFuncLit([], [new JsReturn(variable)]))
	];
	if (!type.castTo!TypeStruct) {
		auto argument = new JsVariable(defaultNaming("value"));
		common ~= Tuple!(string, JsExpr)("set", new JsFuncLit([argument],
				[new JsBinary!"="(variable, argument)]));
	}
	return new JsObject(common);
}

JsExpr castInt(JsExpr expr, Type type) {
	type = type;
	if (auto i = type.castTo!TypeInt) {
		if (i.signed) {
			if (i.size == 8) {
				assert(0, "todo support size" ~ i.size.to!string);
			} else if (i.size == 16) {
				assert(0, "todo support size" ~ i.size.to!string);
			} else if (i.size == 32 || i.size == 0) {
				return new JsBinary!"|"(expr, new JsIntLit(0));
			} else {
				assert(0, "todo support size" ~ i.size.to!string);
			}
		} else {
			if (i.size == 8) {
				return new JsBinary!"&"(expr, new JsIntLit(0xff));
			} else if (i.size == 16) {
				return new JsBinary!"&"(expr, new JsIntLit(0xffff));
			} else if (i.size == 32 || i.size == 0) {
				return new JsBinary!"&"(expr, new JsIntLit(0xffffffff));
			} else {
				assert(0, "todo support size" ~ i.size.to!string);
			}
		}
	} else {
		assert(0);
	}
}

JsExpr compare(JsExpr left, JsExpr right, Type type, Extra extra) {
	return dispatch!(compareImpl, TypeBool, TypeChar, TypeInt, TypeFunction,
			TypePointer, TypeArray, TypeStruct)(type, left, right, extra);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, Extra extra)
		if (staticIndexOf!(T, TypeBool, TypeChar, TypeInt, TypeFunction, TypePointer) >= 0) {
	return new JsBinary!"=="(left, right);
}

JsExpr compareImpl(T)(T that, JsExpr left, JsExpr right, Extra extra)
		if (staticIndexOf!(T, TypeArray, TypeStruct) >= 0) {
	JsVariable variable;
	if (!(that in extra.compareSymbols)) {
		variable = new JsVariable(defaultNaming("__compare_" ~ that.mangle));
		extra.compareSymbols[that] = variable;
	} else {
		variable = extra.compareSymbols[that];
	}
	return new JsCall(variable, [left, right]);
}

JsFuncLit createCompare(Type that, Extra extra) {
	auto left = new JsVariable(defaultNaming("left"));
	auto right = new JsVariable(defaultNaming("right"));

	auto Function = new JsFuncLit([left, right], []);
	dispatch!(createCompareImpl, TypeArray, TypeStruct)(that, left, right, Function.states, extra);
	return Function;
}

void createCompareImpl(TypeArray that, JsExpr left, JsExpr right, JsScope depend, Extra extra) {
	auto lengthCompare = new JsBinary!"!="(arrayLength(left), arrayLength(right));
	depend.states ~= new JsIf(lengthCompare, [new JsReturn(new JsBoolLit(false))], [
			]);

	auto iterator = new JsVariable(temporary);
	auto For = new JsFor(new JsVarDef(iterator, new JsIntLit(0)),
			new JsBinary!"<"(iterator, arrayLength(left)), new JsPostfix!"++"(iterator), [
			]);
	depend ~= For;

	auto elementComparer = new JsPrefix!"!"(compare(indexArray(left, iterator),
			indexArray(right, iterator), that.array, extra));

	For.states ~= new JsIf(elementComparer, [new JsReturn(new JsBoolLit(false))], [
			]);

	depend ~= new JsReturn(new JsBoolLit(true));
}

void createCompareImpl(TypeStruct that, JsExpr left, JsExpr right, JsScope depend, Extra extra) {
	if (that.values.length == 0) {
		depend ~= new JsReturn(new JsBoolLit(true));
	}
	depend ~= new JsReturn(createCompareImplStruct(0, that, left, right, depend, extra));
}

JsExpr createCompareImplStruct(uint index, TypeStruct that, JsExpr left,
		JsExpr right, JsScope depend, Extra extra) {
	auto head = compare(indexTuple(left, index), indexTuple(right, index),
			that.values[index], extra);
	if (index + 1 == that.values.length) {
		return head;
	} else {
		return new JsBinary!"&&"(head, createCompareImplStruct(index + 1, that,
				left, right, depend, extra));
	}
}

struct AssignContext {
	JsExpr variable; //nullable
	JsVariable fresh; //nullable
	//either variable or fresh must be null
	//null variable means fresh must put into a vardef

	Type type;
}

AssignContext assignNullInit(AssignContext context, JsScope depend, Extra extra) {
	if (!context.variable) {
		depend ~= new JsVarDef(context.fresh, new JsArray());
		context.variable = context.fresh;
		context.fresh = null;
	}
	return context;
}

JsExpr assign(AssignContext context, JsExpr variable, JsScope depend, Extra extra) {
	return dispatch!(assignImpl, TypeBool, TypeChar, TypeInt, TypePointer,
			TypeArray, TypeFunction, TypeStruct)(context.type,
			context.variable, context.fresh, variable, depend, extra);
}

JsExpr assignImpl(TypeStruct tuple, JsExpr target, JsVariable fresh,
		JsExpr variable, JsScope depend, Extra extra) {
	if (!target) {
		depend ~= new JsVarDef(fresh, new JsArray());
		target = fresh;
	}
	foreach (c, type; tuple.values) {
		auto index = new JsIntLit(c);
		auto context = AssignContext(new JsIndex(target, index), null, type);
		assign(context, new JsIndex(variable, index), depend, extra);
	}
	return target;
}

JsExpr assignImpl(T)(T type, JsExpr target, JsVariable fresh, JsExpr variable,
		JsScope depend, Extra extra) if (!is(T == TypeStruct)) {
	if (target) {
		depend ~= new JsBinary!"="(target, variable);
		return target;
	} else {
		depend ~= new JsVarDef(fresh, variable);
		return fresh;
	}
}

JsExpr generateJsImpl(IntLit that, Usage usage, JsScope depend, Extra extra) {
	return new JsIntLit(that.value.to!long);
}

JsExpr generateJsImpl(ExternJs that, Usage usage, JsScope depend, Extra extra) {
	return new JsExternLit(that.name);
}

//only have a generateinto
alias VariableOutput = AliasSeq!(If, NewArray);

JsExpr generateJsImpl(T)(T that, Usage usage, JsScope depend, Extra extra)
		if (staticIndexOf!(T, VariableOutput) >= 0) {
	return createVarAndGenerateInto(that, depend, extra);
}

JsExpr createVarAndGenerateInto(T)(T that, JsScope depend, Extra extra) {
	auto variable = new JsVariable(temporary);
	auto target = AssignContext(null, variable, that.type);
	generateJsIntoImpl(that, target, depend, extra);
	return variable;
}

void generateJsIntoImpl(T)(T that, AssignContext target, JsScope depend, Extra extra)
		if (staticIndexOf!(T, VariableOutput) < 0) {
	auto variable = that.generateJs(Usage(true), depend, extra);
	assign(target, variable, depend, extra);
}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra extra)
		if (staticIndexOf!(T, BoolLit, CharLit, ScopeVarClass!true, ModuleVarRef,
			FuncArgument, StringLit, IntLit, ExternJs, FunctionLiteral) >= 0) {

}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra extra)
		if (staticIndexOf!(T, New, CastInteger, Length, Prefix!"-", Deref,
			Address, Prefix!"!") >= 0) {
	that.value.generateJsEffectsOnly(depend, extra);
}

void generateJsEffectsOnlyImpl(string op)(Binary!op that, JsScope depend, Extra extra) {
	that.left.generateJsEffectsOnly(depend, extra);
	that.right.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(BoolLit that, Usage usage, JsScope depend, Extra extra) {
	if (that.yes) {
		return new JsBoolLit(true);
	} else {
		return new JsBoolLit(false);
	}
}

JsExpr generateJsImpl(CharLit that, Usage usage, JsScope depend, Extra extra) {
	return new JsCharLit(that.value);
}

JsExpr generateJsImpl(TupleLit that, Usage usage, JsScope depend, Extra extra) {
	return new JsArray(that.values.map!(a => a.generateJs(usage, depend, extra)).array);
}

void generateJsEffectsOnlyImpl(TupleLit that, JsScope depend, Extra extra) {
	that.values.each!(a => a.generateJsEffectsOnly(depend, extra));
}

JsExpr generateJsImpl(ModuleVarRef that, Usage usage, JsScope depend, Extra extra) {
	return extra.symbols[that.definition];
}

JsExpr generateJsImpl(ScopeVarClass!true that, Usage usage, JsScope depend, Extra extra) {
	return extra.context.variables[that];
}

JsExpr generateJsImpl(FuncArgument that, Usage usage, JsScope, Extra extra) {
	return extra.context.argument;
}

void generateJsIntoImpl(If that, AssignContext target, JsScope depend, Extra extra) {
	auto If = new JsIf();
	target = assignNullInit(target, depend, extra);
	If.cond = that.cond.generateJs(Usage(true), depend, extra);
	that.yes.generateJsInto(target, If.yes, extra);
	that.no.generateJsInto(target, If.no, extra);
	depend ~= If;
}

void generateJsEffectsOnlyImpl(If that, JsScope depend, Extra extra) {
	auto If = new JsIf();
	If.cond = that.cond.generateJs(Usage(true), depend, extra);
	that.yes.generateJsEffectsOnly(If.yes, extra);
	that.no.generateJsEffectsOnly(If.no, extra);
	depend ~= If;
}

JsExpr generateJsImpl(While that, Usage usage, JsScope depend, Extra extra) {
	auto While = new JsWhile();
	auto cond = that.cond.generateJs(Usage(true), While.states, extra);

	if (While.states.length == 0) {
		While.cond = cond;
		that.state.generateJsEffectsOnly(While.states, extra);
	} else {
		While.cond = new JsBoolLit(true);
		While.states ~= new JsIf(new JsPrefix!"!"(cond), [new JsBreak()], []);
		that.state.generateJsEffectsOnly(While.states, extra);
	}
	depend ~= While;
	return new JsArray([]);
}

void generateJsEffectsOnlyImpl(While that, JsScope depend, Extra extra) {
	generateJsImpl(that, Usage(true), depend, extra);
}

JsExpr generateJsImpl(New that, Usage usage, JsScope depend, Extra extra) {
	if (usage.sideEffects) {
		auto variable = new JsVariable(temporary);
		auto target = AssignContext(null, variable, that.value.type);
		that.value.generateJsInto(target, depend, extra);
		return createLocalPointer(that.value.type, variable);
	} else {
		return createVarAndGenerateInto(that, depend, extra);
	}
}

void generateJsIntoImpl(NewArray that, AssignContext target, JsScope depend, Extra extra) {
	auto length = that.length.generateJs(Usage(false), depend, extra);
	auto expression = that.value.generateJs(Usage(false), depend, extra);
	auto variable = assign(target, new JsArray(), depend, extra);
	auto iterator = new JsVariable(temporary);
	auto loop = new JsFor(new JsVarDef(iterator, new JsIntLit(0)),
			new JsBinary!"<"(iterator, length), new JsPostfix!"++"(iterator), []);
	assign(AssignContext(new JsIndex(variable, iterator), null,
			that.value.type), expression, depend, extra);
	depend ~= loop;
}

void generateJsEffectsOnlyImpl(NewArray that, JsScope depend, Extra extra) {
	that.value.generateJsEffectsOnly(depend, extra);
	that.length.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(CastInteger that, Usage usage, JsScope depend, Extra extra) {
	auto value = that.value.generateJs(usage, depend, extra);
	return castInt(value, that.type);
}

JsExpr generateJsImpl(Length that, Usage usage, JsScope depend, Extra extra) {
	auto value = that.value.generateJs(usage, depend, extra);
	return arrayLength(value);
}

JsExpr generateJsImpl(Index that, Usage usage, JsScope depend, Extra extra) {
	auto array = that.array.generateJs(Usage(false), depend, extra);
	auto index = that.index.generateJs(Usage(false), depend, extra);
	return indexArray(array, index);
}

JsExpr generateJsImpl(bool lvalue)(TupleIndex!lvalue that, Usage usage, JsScope depend, Extra extra) {
	auto tuple = that.tuple.generateJs(usage, depend, extra);
	return indexTuple(tuple, that.index);
}

void generateJsEffectsOnlyImpl(Index that, JsScope depend, Extra extra) {
	that.array.generateJsEffectsOnly(depend, extra);
	that.index.generateJsEffectsOnly(depend, extra);
}

void generateJsEffectsOnlyImpl(bool lvalue)(TupleIndex!lvalue that, JsScope depend, Extra extra) {
	that.tuple.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(Call that, Usage usage, JsScope depend, Extra extra) {
	if (usage.sideEffects) {
		auto functionPointer = that.calle.generateJs(Usage(true), depend, extra);
		auto argument = that.argument.generateJs(Usage(true), depend, extra);
		auto expression = new JsCall(functionPointer, [argument]);
		return expression;
	} else {
		return createVarAndGenerateInto(that, depend, extra);
	}
}

void generateJsEffectsOnlyImpl(Call that, JsScope depend, Extra extra) {
	auto functionPointer = that.calle.generateJs(Usage(true), depend, extra);
	auto argument = that.argument.generateJs(Usage(true), depend, extra);
	depend ~= new JsCall(functionPointer, [argument]);
}

JsExpr generateJsImpl(Slice that, Usage usage, JsScope depend, Extra extra) {
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

void generateJsEffectsOnlyImpl(Slice that, JsScope depend, Extra extra) {
	that.array.generateJsEffectsOnly(depend, extra);
	that.left.generateJsEffectsOnly(depend, extra);
	that.right.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(StringLit that, Usage usage, JsScope depend, Extra extra) {
	return new JsArray(that.value
			.map!(a => new JsCharLit(a))
			.map!(a => a.convert!JsExpr)
			.array);
}

JsExpr generateJsImpl(ArrayLit that, Usage usage, JsScope depend, Extra extra) {
	if (usage.sideEffects) {
		//todo fix me
		if (that.values.length > 0 && that.values[0].type.castTo!(TupleLit)) {
			assert(0, "tuple lit arrays not supported yet");
		}
		return new JsArray(that.values.map!(a => a.generateJs(Usage(true), depend, extra)).array);
	} else {
		return createVarAndGenerateInto(that, depend, extra);
	}
}

void generateJsEffectsOnlyImpl(ArrayLit that, JsScope depend, Extra extra) {
	that.values.each!(a => a.generateJsEffectsOnly(depend, extra));
}

JsExpr generateJsImpl(Binary!"==" that, Usage usage, JsScope depend, Extra extra) {
	auto left = that.left.generateJs(usage, depend, extra);
	auto right = that.right.generateJs(usage, depend, extra);
	return compare(left, right, that.left.type, extra);
}

JsExpr generateJsImpl(Binary!"!=" that, Usage usage, JsScope depend, Extra extra) {
	auto left = that.left.generateJs(usage, depend, extra);
	auto right = that.right.generateJs(usage, depend, extra);
	return new JsPrefix!"!"(compare(left, right, that.left.type, extra));
}

JsExpr generateJsImpl(Binary!"~" that, Usage usage, JsScope depend, Extra extra) {
	assert(0, "todo implement ~");
}

JsExpr generateJsImpl(Deref that, Usage usage, JsScope depend, Extra extra) {
	return getPointer(that.value.generateJs(usage, depend, extra));
}

JsExpr generateJsImpl(Address that, Usage usage, JsScope depend, Extra extra) {
	return that.value.generateJsAddressOf(usage, depend, extra);
}

JsExpr generateJsAddressOfImpl(ScopeVarClass!true that0, Usage usage, JsScope depend, Extra extra) {
	auto that = that0.convert!ScopeVar;
	if (that in extra.context.localPointers) {
		return extra.context.localPointers[that];
	}
	auto pointer = new JsVariable(temporary);
	extra.context.variableScopes[that] ~= new JsVarDef(pointer,
			createLocalPointer(that.type, extra.context.variables[that]));
	extra.context.localPointers[that] = pointer;
	return pointer;
}

JsExpr generateJsAddressOfImpl(ModuleVarRef that, Usage usage, JsScope depend, Extra extra) {
	assert(0, "todo implement module pointers");
}

JsExpr generateJsAddressOfImpl(Index that, Usage usage, JsScope depend, Extra extra) {
	auto array = that.array.generateJs(Usage(false), depend, extra);
	auto index = that.index.generateJs(Usage(false), depend, extra);
	getOrCreateArrayPointer(that.type, array, index, depend);
	return indexPointerArray(array, index);
}

JsExpr generateJsAddressOfImpl(TupleIndex!true that, Usage usage, JsScope depend, Extra extra) {
	auto tuple = that.tuple.generateJs(Usage(false), depend, extra);
	getOrCreateTuplePointer(that.type, tuple, that.index, depend);
	return indexTuplePointer(tuple, that.index);
}

JsExpr generateJsAddressOfImpl(Deref that, Usage usage, JsScope depend, Extra extra) {
	return that.value.generateJs(usage, depend, extra);
}

JsExpr generateJsImpl(Scope that, Usage usage, JsScope depend, Extra extra) {
	that.pass.generateJsEffectsOnly(depend, extra);
	return that.last.generateJs(usage, depend, extra);
}

void generateJsEffectsOnlyImpl(Scope that, JsScope depend, Extra extra) {
	that.pass.generateJsEffectsOnly(depend, extra);
	that.last.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(ScopeVarDef that, Usage usage, JsScope depend, Extra extra) {
	auto variable = new JsVariable(defaultNaming(that.variable.name));
	that.variable.value.generateJsInto(AssignContext(null, variable,
			that.variable.type), depend, extra);
	extra.context.variables[that.variable] = variable;
	extra.context.variableScopes[that.variable] = depend;
	return that.last.generateJs(usage, depend, extra);
}

void generateJsEffectsOnlyImpl(ScopeVarDef that, JsScope depend, Extra extra) {
	auto variable = new JsVariable(defaultNaming(that.variable.name));
	that.variable.value.generateJsInto(AssignContext(null, variable,
			that.variable.type), depend, extra);
	extra.context.variables[that.variable] = variable;
	extra.context.variableScopes[that.variable] = depend;
	that.last.generateJsEffectsOnly(depend, extra);
}

JsExpr generateJsImpl(Assign that, Usage usage, JsScope depend, Extra extra) {
	that.left.generateJsAssign(that.right, depend, extra);
	return that.last.generateJs(usage, depend, extra);
}

void generateJsEffectsOnlyImpl(Assign that, JsScope depend, Extra extra) {
	that.left.generateJsAssign(that.right, depend, extra);
	that.last.generateJsEffectsOnly(depend, extra);
}

void generateJsAssignImpl(T)(T that, RuntimeExpression right, JsScope depend, Extra extra)
		if (!is(T == Deref)) {
	auto target = that.generateJs(Usage(false), depend, extra);
	auto context = AssignContext(target, null, that.type);
	right.generateJsInto(context, depend, extra);
}

void generateJsAssignImpl(Deref that, RuntimeExpression right, JsScope depend, Extra extra) {
	dispatch!(generateJsAssignImplType, TypeBool, TypeChar, TypeInt,
			TypePointer, TypeArray, TypeFunction, TypeStruct)(that.type, that, right, depend, extra);
}

void generateJsAssignImplType(TypeStruct type, Deref that,
		RuntimeExpression right, JsScope depend, Extra extra) {
	auto output = that.value.generateJs(Usage(false), depend, extra);
	auto context = AssignContext(output, null, type);
	right.generateJsInto(context, depend, extra);
}

void generateJsAssignImplType(T)(T type, Deref that, RuntimeExpression right,
		JsScope depend, Extra extra) {
	auto target = right.generateJs(Usage(true), depend, extra);
	auto output = that.value.generateJs(Usage(true), depend, extra);
	depend ~= setPointer(output, target);
}

JsExpr generateJsImpl(FunctionLiteral that, Usage usage, JsScope depend, Extra extra) {
	return extra.symbols[that];
}

JsExpr generateJsImpl(string op)(Binary!op that, Usage usage, JsScope depend, Extra extra)
		if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = that.left.generateJs(usage, depend, extra);
	auto right = that.right.generateJs(usage, depend, extra);
	return castInt(new JsBinary!op(left, right), that.type);
}

JsExpr generateJsImpl(string op)(Binary!op that, Usage usage, JsScope depend, Extra extra)
		if (["<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
	auto left = that.left.generateJs(usage, depend, extra);
	auto right = that.right.generateJs(usage, depend, extra);
	return new JsBinary!op(left, right);
}

JsExpr generateJsImpl(string op)(Prefix!op that, Usage usage, JsScope depend, Extra extra)
		if (["-", "!"].canFind(op)) {
	return new JsPrefix!op(that.value.generateJs(usage, depend, extra));
}
