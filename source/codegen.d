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
	if (extra.tuplePointer) {
		depend ~= new JsVarDef(extra.tuplePointer, createTuplePointerFunction(extra));
	}
	if (extra.arrayPointer) {
		depend ~= new JsVarDef(extra.arrayPointer, createArrayPointerFunction(extra));
	}
}

JsExpr generateSymbolImpl(ModuleVarDef that, JsScope depend, Extra extra) {
	extra.context = FunctionContext();
	return that.value.generateJs(depend, extra);
}

JsExpr generateSymbolImpl(FunctionLiteral that, JsScope depend, Extra extra) {
	extra.context = FunctionContext();
	extra.context.argument = new JsVariable(temporary);
	auto result = new JsFuncLit([extra.context.argument], []);
	if (!sameType(that.text.type, new TypeStruct())) {
		auto val = that.text.generateJs(result.states, extra);
		result.states ~= new JsReturn(val);
	} else {
		that.text.generateJsEffectsOnly(result.states, extra);
	}

	return result;
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
	JsVariable tuplePointer;
	JsVariable arrayPointer;
	JsVariable[Symbol] symbols;

	JsVariable getCompare(Type type) {
		JsVariable variable;
		if (!(type in compareSymbols)) {
			variable = new JsVariable(defaultNaming("typi_compare_" ~ type.mangle));
			compareSymbols[type] = variable;
		} else {
			variable = compareSymbols[type];
		}
		return variable;
	}

	JsVariable getTuplePointer() {
		if (tuplePointer is null) {
			tuplePointer = new JsVariable(defaultNaming("typi_tuple_address_of"));
		}
		return tuplePointer;
	}

	JsVariable getArrayPointer() {
		if (arrayPointer is null) {
			arrayPointer = new JsVariable(defaultNaming("typi_array_address_of"));
		}
		return arrayPointer;
	}
}

JsExpr indexTuple(JsExpr tuple, JsExpr index) {
	return new JsIndex(tuple, index);
}

JsExpr indexTuple(JsExpr tuple, size_t index) {
	return indexTuple(tuple, new JsIntLit(index));
}

JsExpr indexTuplePointer(JsExpr tuple, JsExpr index) {
	return new JsIndex(new JsDot(tuple, "ptr"), index);
}

JsExpr createTuplePointer(JsExpr tuple, JsExpr index) {
	auto variable = new JsVariable(defaultNaming("value"));
	return new JsObject([
			Tuple!(string, JsExpr)("tuple", tuple),
			Tuple!(string, JsExpr)("get", new JsFuncLit([],
				[new JsReturn(indexTuple(new JsDot(new JsThis(), "tuple"), index))])),
			Tuple!(string, JsExpr)("set", new JsFuncLit([variable],
				[
					new JsBinary!"="(indexTuple(new JsDot(new JsThis(), "tuple"), index), variable)
				]))
			]);
}

void getOrCreateTuplePointer(JsExpr tuple, JsExpr index, JsScope depend) {
	depend ~= new JsBinary!"="(new JsDot(tuple, "ptr"),
			new JsBinary!"||"(new JsDot(tuple, "ptr"), new JsArray()));
	depend ~= new JsBinary!"="(indexTuplePointer(tuple, index),
			new JsBinary!"||"(indexTuplePointer(tuple, index), createTuplePointer(tuple, index)));
}

JsFuncLit createTuplePointerFunction(Extra extra) {
	auto tuple = new JsVariable(defaultNaming("tuple"));
	auto index = new JsVariable(defaultNaming("index"));

	JsFuncLit func = new JsFuncLit([tuple, index], []);
	getOrCreateTuplePointer(tuple, index, func.states);
	func.states ~= new JsReturn(indexTuplePointer(tuple, index));
	return func;
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

JsExpr indexArrayPointer(JsExpr array, JsExpr index) {
	return new JsIndex(new JsDot(internalArray(array), "ptr"),
			new JsBinary!"+"(arrayStart(array), index));
}

JsExpr createArrayPointer(JsExpr array, JsExpr index) {
	auto variable = new JsVariable(defaultNaming("value"));
	return new JsObject([
			Tuple!(string, JsExpr)("array", array),
			Tuple!(string, JsExpr)("get", new JsFuncLit([],
				[new JsReturn(indexArray(new JsDot(new JsThis(), "array"), index))])),
			Tuple!(string, JsExpr)("set", new JsFuncLit([variable],
				[
					new JsBinary!"="(indexArray(new JsDot(new JsThis(), "array"), index), variable)
				]))
			]);
}

void getOrCreateArrayPointer(JsExpr array, JsExpr index, JsScope depend) {
	depend ~= new JsBinary!"="(new JsDot(internalArray(array), "ptr"),
			new JsBinary!"||"(new JsDot(internalArray(array), "ptr"), new JsArray()));
	depend ~= new JsBinary!"="(indexArrayPointer(array, index),
			new JsBinary!"||"(indexArrayPointer(array, index), createArrayPointer(array, index)));
}

JsFuncLit createArrayPointerFunction(Extra extra) {
	auto array = new JsVariable(defaultNaming("array"));
	auto index = new JsVariable(defaultNaming("index"));

	JsFuncLit func = new JsFuncLit([array, index], []);
	getOrCreateArrayPointer(array, index, func.states);
	func.states ~= new JsReturn(indexArrayPointer(array, index));
	return func;
}

JsExpr getPointer(JsExpr pointer) {
	return new JsCall(new JsDot(pointer, "get"), []);
}

JsExpr setPointer(JsExpr pointer, JsExpr value) {
	return new JsCall(new JsDot(pointer, "set"), [value]);
}

JsExpr createLocalPointer(Type type, JsExpr variable) {
	if (type.castTo!TypeStruct) {
		return variable;
	} else {
		auto argument = new JsVariable(defaultNaming("value"));
		auto common = [
			Tuple!(string, JsExpr)("get", new JsFuncLit([],
					[new JsReturn(variable)])),
			Tuple!(string, JsExpr)("set", new JsFuncLit([argument],
					[new JsBinary!"="(variable, argument)]))
		];
		return new JsObject(common);
	}
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
	return new JsCall(extra.getCompare(that), [left, right]);
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

JsExpr clone(Type that, JsExpr expression) {
	return dispatch!(cloneImpl, TypeBool, TypeChar, TypeInt, TypePointer,
			TypeArray, TypeFunction, TypeStruct)(that, expression);
}

JsExpr cloneImpl(TypeStruct that, JsExpr expression) {
	return new JsArray(that.values.enumerate.map!(a => indexTuple(clone(a[1],
			expression), a[0])).array);
}

JsExpr cloneImpl(T)(T that, JsExpr expression) if (!is(T == TypeStruct)) {
	return expression;
}

void copy(Type that, JsExpr to, JsExpr from, void delegate(JsExpr to, JsExpr from) assign) {
	return dispatch!(copyImpl, TypeBool, TypeChar, TypeInt, TypePointer,
			TypeArray, TypeFunction, TypeStruct)(that, to, from, assign);
}

void copyImpl(TypeStruct tuple, JsExpr to, JsExpr from, void delegate(JsExpr to, JsExpr from) assign) {
	foreach (c, type; tuple.values) {
		copy(type, new JsIndex(to, new JsIntLit(c)), new JsIndex(from, new JsIntLit(c)), assign);
	}
}

void copyImpl(T)(T, JsExpr to, JsExpr from, void delegate(JsExpr to, JsExpr from) assign)
		if (!is(T == TypeStruct)) {
	assign(to, from);
}

void delegate(JsExpr to, JsExpr from) regularAssign(JsScope depend) {
	return (to, from) { depend ~= new JsBinary!"="(to, from); };
}

enum Default(T) = staticIndexOf!(T, Pures) < 0 && staticIndexOf!(T, Dependents!false) < 0
	&& staticIndexOf!(T, Dependents!true) < 0 && staticIndexOf!(T, VariableOutput) < 0;

alias Pures = AliasSeq!(Index, ModuleVarRef, ScopeVarClass!true, FunctionLiteral,
		IntLit, ExternJs, BoolLit, CharLit, FuncArgument, StringLit, While, Slice);
enum Pure(T) = staticIndexOf!(T, Pures) >= 0;

alias Dependents(bool copy : false) = AliasSeq!(CastInteger, Length, TupleIndex!true,
		TupleIndex!false, Binary!"==", Binary!"!=", staticMap!(Binary, "*",
			"/", "%", "+", "-"), staticMap!(Binary, "<=", ">=", "<", ">",
			"&&", "||"), Prefix!"!", Prefix!"-",);
enum Dependent(T) = staticIndexOf!(T, Dependents!false) >= 0;

alias Dependents(bool copy : true) = AliasSeq!(TupleLit, Scope, ScopeVarDef, Assign);

enum DependentCopy(T) = staticIndexOf!(T, Dependents!true) >= 0;

alias VariableOutput = AliasSeq!(If, NewArray);
enum Variable(T) = staticIndexOf!(T, VariableOutput) >= 0;

JsExpr generateJsEffectLessImpl(T)(T that, JsScope depend, Extra extra)
		if (Default!T) {
	auto variable = new JsVariable(temporary);
	depend ~= new JsVarDef(variable, generateJsImpl(that, depend, extra));
	return variable;
}

JsExpr generateJsCopyImpl(T)(T that, JsScope depend, Extra extra)
		if (Default!T || Pure!T || Variable!T || Dependent!T) {
	if (that.type.castTo!TypeStruct) {
		return clone(that.type, generateJsEffectLessImpl(that, depend, extra));
	} else {
		return generateJsImpl(that, depend, extra);
	}
}

JsExpr generateJsEffectLessCopyImpl(T)(T that, JsScope depend, Extra extra)
		if (Default!T || Pure!T || Dependent!T || Variable!T) {
	return clone(that.type, generateJsEffectLessImpl(that, depend, extra));
}

void generateJsVarImpl(T)(T that, JsVariable target, JsScope depend, Extra extra)
		if (Default!T || Pure!T || Dependent!T || DependentCopy!T) {
	depend ~= new JsVarDef(target, generateJsCopyImpl(that, depend, extra));
}

void generateJsExprImpl(T)(T that, JsExpr target, JsScope depend, Extra extra)
		if (Default!T || Pure!T || Dependent!T || DependentCopy!T) {
	auto expression = generateJsEffectLessImpl(that, depend, extra);
	copy(that.type, target, expression, regularAssign(depend));
}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra extra)
		if (Default!T || Variable!T && !is(T == If)) {
	depend ~= generateJsImpl(that, depend, extra);
}

JsExpr generateJsImpl(T)(T that, JsScope depend, Extra extra) if (Pure!T) {
	return generateJsPure(that, depend, extra);
}

JsExpr generateJsEffectLessImpl(T)(T that, JsScope depend, Extra extra) if (Pure!T) {
	return generateJsPure(that, depend, extra);
}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra extra) if (Pure!T) {
	generateJsPure(that, depend, extra);
}

JsExpr generateJsImpl(T)(T that, JsScope depend, Extra extra)
		if (Dependent!T || DependentCopy!T) {
	return generateJsDependent!((a, depend, extra) => a.generateJs(depend, extra))(that,
			depend, extra);
}

JsExpr generateJsEffectLessImpl(T)(T that, JsScope depend, Extra extra)
		if (Dependent!T || DependentCopy!T) {
	return generateJsDependent!((a, depend, extra) => a.generateJsEffectLess(depend, extra))(that,
			depend, extra);
}

JsExpr generateJsCopyImpl(T)(T that, JsScope depend, Extra extra)
		if (DependentCopy!T) {
	return generateJsDependent!((a, depend, extra) => a.generateJsCopy(depend, extra))(that,
			depend, extra);
}

JsExpr generateJsEffectLessCopyImpl(T)(T that, JsScope depend, Extra extra)
		if (DependentCopy!T) {
	return generateJsDependent!((a, depend, extra) => a.generateJsEffectLessCopy(depend, extra))(that,
			depend, extra);
}

void generateJsEffectsOnlyImpl(T)(T that, JsScope depend, Extra extra)
		if (Dependent!T || DependentCopy!T) {
	generateJsDependent!((a, depend, extra) {
		a.generateJsEffectsOnly(depend, extra);
		return cast(JsExpr) null;
	})(that, depend, extra);
}

JsExpr generateJsImpl(T)(T that, JsScope depend, Extra extra) if (Variable!T) {
	return generateJsEffectLessImpl(that, depend, extra);
}

JsExpr generateJsEffectLessImpl(T)(T that, JsScope depend, Extra extra)
		if (Variable!T) {
	auto variable = new JsVariable(temporary);
	depend ~= new JsVarDef(variable, new JsArray([]));
	generateJsExprImpl(that, variable, depend, extra);
	return variable;
}

JsExpr generateJsPure(IntLit that, JsScope depend, Extra extra) {
	return new JsIntLit(that.value.to!long);
}

JsExpr generateJsPure(ExternJs that, JsScope depend, Extra extra) {
	return new JsExternLit(that.name);
}

JsExpr generateJsPure(BoolLit that, JsScope depend, Extra extra) {
	if (that.yes) {
		return new JsBoolLit(true);
	} else {
		return new JsBoolLit(false);
	}
}

JsExpr generateJsPure(CharLit that, JsScope depend, Extra extra) {
	return new JsCharLit(that.value);
}

JsExpr generateJsDependent(alias generate)(TupleLit that, JsScope depend, Extra extra) {
	return new JsArray(that.values.map!(a => generate(a, depend, extra)).array);
}

JsExpr generateJsPure(ModuleVarRef that, JsScope depend, Extra extra) {
	return extra.symbols[that.definition];
}

JsExpr generateJsPure(ScopeVarClass!true that, JsScope depend, Extra extra) {
	return extra.context.variables[that];
}

JsExpr generateJsPure(FuncArgument that, JsScope, Extra extra) {
	return extra.context.argument;
}

void generateJsVarImpl(If that, JsVariable target, JsScope depend, Extra extra) {
	auto If = new JsIf();
	depend ~= new JsVarDef(target, new JsArray([])); // todo defined
	If.cond = that.cond.generateJs(depend, extra);
	that.yes.generateJsExpr(target, If.yes, extra);
	that.no.generateJsExpr(target, If.no, extra);
	depend ~= If;
}

void generateJsExprImpl(If that, JsExpr target, JsScope depend, Extra extra) {
	auto If = new JsIf();
	If.cond = that.cond.generateJs(depend, extra);
	that.yes.generateJsExpr(target, If.yes, extra);
	that.no.generateJsExpr(target, If.no, extra);
	depend ~= If;
}

void generateJsEffectsOnlyImpl(If that, JsScope depend, Extra extra) {
	auto If = new JsIf();
	If.cond = that.cond.generateJs(depend, extra);
	that.yes.generateJsEffectsOnly(If.yes, extra);
	that.no.generateJsEffectsOnly(If.no, extra);
	depend ~= If;
}

JsExpr generateJsPure(While that, JsScope depend, Extra extra) {
	auto While = new JsWhile();
	auto cond = that.cond.generateJs(While.states, extra);

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

JsExpr generateJsImpl(New that, JsScope depend, Extra extra) {
	auto variable = new JsVariable(temporary);
	that.value.generateJsVar(variable, depend, extra);
	return createLocalPointer(that.value.type, variable);
}

void generateJsVarImpl(NewArray that, JsVariable target, JsScope depend, Extra extra) {
	auto length = that.length.generateJsEffectLess(depend, extra);
	auto expression = that.value.generateJsEffectLessCopy(depend, extra);
	depend ~= new JsVarDef(target, new JsArray([]));
	auto iterator = new JsVariable(temporary);
	auto loop = new JsFor(new JsVarDef(iterator, new JsIntLit(0)),
			new JsBinary!"<"(iterator, length), new JsPostfix!"++"(iterator), []);
	loop.states ~= new JsBinary!"="(new JsIndex(target, iterator), expression);
	depend ~= loop;
}

void generateJsExprImpl(NewArray that, JsExpr target, JsScope depend, Extra extra) {
	auto length = that.length.generateJsEffectLess(depend, extra);
	auto expression = that.value.generateJsEffectLessCopy(depend, extra);
	depend ~= new JsBinary!"="(target, new JsArray([]));
	auto iterator = new JsVariable(temporary);
	auto loop = new JsFor(new JsVarDef(iterator, new JsIntLit(0)),
			new JsBinary!"<"(iterator, length), new JsPostfix!"++"(iterator), []);
	loop.states ~= new JsBinary!"="(new JsIndex(target, iterator), expression);
	depend ~= loop;
}

JsExpr generateJsDependent(alias generate)(CastInteger that, JsScope depend, Extra extra) {
	auto value = generate(that.value, depend, extra);
	return castInt(value, that.type);
}

JsExpr generateJsDependent(alias generate)(Length that, JsScope depend, Extra extra) {
	auto value = generate(that.value, depend, extra);
	return arrayLength(value);
}

JsExpr generateJsPure(Index that, JsScope depend, Extra extra) {
	auto array = that.array.generateJsEffectLess(depend, extra);
	auto index = that.index.generateJsEffectLess(depend, extra);
	return indexArray(array, index);
}

JsExpr generateJsDependent(alias generate, bool lvalue)(TupleIndex!lvalue that,
		JsScope depend, Extra extra) {
	auto tuple = generate(that.tuple, depend, extra);
	return indexTuple(tuple, that.index);
}

JsExpr generateJsImpl(Call that, JsScope depend, Extra extra) {
	auto functionPointer = that.calle.generateJs(depend, extra);
	auto argument = that.argument.generateJs(depend, extra);
	auto expression = new JsCall(functionPointer, [argument]);
	return expression;
}

JsExpr generateJsPure(Slice that, JsScope depend, Extra extra) {
	auto array = that.array.generateJsEffectLess(depend, extra);
	auto left = that.left.generateJsEffectLess(depend, extra);
	auto right = that.right.generateJsEffectLess(depend, extra);
	return new JsObject([
			Tuple!(string, JsExpr)("data", internalArray(array)),
			Tuple!(string, JsExpr)("start", new JsBinary!"+"(arrayStart(array),
				left)),
			Tuple!(string, JsExpr)("length", new JsBinary!"-"(right, left))
			]);
}

JsExpr generateJsPure(StringLit that, JsScope depend, Extra extra) {
	return new JsArray(that.value
			.map!(a => new JsCharLit(a))
			.map!(a => a.convert!JsExpr)
			.array);
}

JsExpr generateJsImpl(ArrayLit that, JsScope depend, Extra extra) {
	return new JsArray(that.values.map!(a => a.generateJsCopy(depend, extra)).array);
}

JsExpr generateJsDependent(alias generate)(Binary!"==" that, JsScope depend, Extra extra) {
	auto left = generate(that.left, depend, extra);
	auto right = generate(that.right, depend, extra);
	return compare(left, right, that.left.type, extra);
}

JsExpr generateJsDependent(alias generate)(Binary!"!=" that, JsScope depend, Extra extra) {
	auto left = generate(that.left, depend, extra);
	auto right = generate(that.right, depend, extra);
	return new JsPrefix!"!"(compare(left, right, that.left.type, extra));
}

JsExpr generateJsImpl(Binary!"~" that, JsScope depend, Extra extra) {
	assert(0, "todo implement ~");
}

JsExpr generateJsImpl(Deref that, JsScope depend, Extra extra) {
	if (that.type.castTo!TypeStruct) {
		return that.value.generateJs(depend, extra);
	} else {
		return getPointer(that.value.generateJs(depend, extra));
	}
}

JsExpr generateJsImpl(Address that, JsScope depend, Extra extra) {
	if (that.value.type.castTo!TypeStruct) {
		return that.value.generateJs(depend, extra);
	} else {
		return that.value.generateJsAddressOf(depend, extra);
	}
}

JsExpr generateJsAddressOfImpl(ScopeVarClass!true that0, JsScope depend, Extra extra) {
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

JsExpr generateJsAddressOfImpl(ModuleVarRef that, JsScope depend, Extra extra) {
	assert(0, "todo implement module pointers");
}

JsExpr generateJsAddressOfImpl(Index that, JsScope depend, Extra extra) {
	auto array = that.array.generateJsEffectLess(depend, extra);
	auto index = that.index.generateJsEffectLess(depend, extra);
	return new JsCall(extra.getArrayPointer, [array, index]);
}

JsExpr generateJsAddressOfImpl(TupleIndex!true that, JsScope depend, Extra extra) {
	auto tuple = that.tuple.generateJsEffectLess(depend, extra);
	return new JsCall(extra.getTuplePointer, [tuple, new JsIntLit(that.index)]);
}

JsExpr generateJsAddressOfImpl(Deref that, JsScope depend, Extra extra) {
	return that.value.generateJs(depend, extra);
}

JsExpr generateJsDependent(alias generate)(Scope that, JsScope depend, Extra extra) {
	that.pass.generateJsEffectsOnly(depend, extra);
	return generate(that.last, depend, extra);
}

JsExpr generateJsDependent(alias generate)(ScopeVarDef that, JsScope depend, Extra extra) {
	auto variable = new JsVariable(defaultNaming(that.variable.name));
	that.variable.value.generateJsVar(variable, depend, extra);
	extra.context.variables[that.variable] = variable;
	extra.context.variableScopes[that.variable] = depend;
	return generate(that.last, depend, extra);
}

JsExpr generateJsDependent(alias generate)(Assign that, JsScope depend, Extra extra) {
	that.left.generateJsAssign(that.right, depend, extra);
	return generate(that.last, depend, extra);
}

void generateJsAssignImpl(Index that, RuntimeExpression right, JsScope depend, Extra extra) {
	auto array = that.array.generateJsEffectLess(depend, extra);
	auto index = that.index.generateJsEffectLess(depend, extra);
	right.generateJsExpr(indexArray(array, index), depend, extra);
}

void generateJsAssignImpl(TupleIndex!true that, RuntimeExpression right, JsScope depend, Extra extra) {
	auto tuple = that.tuple.generateJsEffectLess(depend, extra);
	right.generateJsExpr(indexTuple(tuple, that.index), depend, extra);
}

void generateJsAssignImpl(ScopeVarClass!true that, RuntimeExpression right,
		JsScope depend, Extra extra) {
	auto target = that.generateJs(depend, extra);
	right.generateJsExpr(target, depend, extra);
}

void generateJsAssignImpl(ModuleVarRef that, RuntimeExpression right, JsScope depend, Extra extra) {
	auto target = that.generateJs(depend, extra);
	right.generateJsExpr(target, depend, extra);
}

void generateJsAssignImpl(Deref that, RuntimeExpression right, JsScope depend, Extra extra) {
	dispatch!(generateJsAssignImplType, TypeBool, TypeChar, TypeInt,
			TypePointer, TypeArray, TypeFunction, TypeStruct)(that.type, that, right, depend, extra);
}

void generateJsAssignImplType(TypeStruct type, Deref that,
		RuntimeExpression right, JsScope depend, Extra extra) {
	auto output = that.value.generateJsEffectLess(depend, extra);
	right.generateJsExpr(output, depend, extra);
}

void generateJsAssignImplType(T)(T type, Deref that, RuntimeExpression right,
		JsScope depend, Extra extra) if (!is(T == TypeStruct)) {
	auto target = right.generateJs(depend, extra);
	auto output = that.value.generateJs(depend, extra);
	depend ~= setPointer(output, target);
}

JsExpr generateJsPure(FunctionLiteral that, JsScope depend, Extra extra) {
	return extra.symbols[that];
}

JsExpr generateJsDependent(alias generate, string op)(Binary!op that, JsScope depend, Extra extra)
		if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = generate(that.left, depend, extra);
	auto right = generate(that.right, depend, extra);
	return castInt(new JsBinary!op(left, right), that.type);
}

JsExpr generateJsDependent(alias generate, string op)(Binary!op that, JsScope depend, Extra extra)
		if (["<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
	auto left = generate(that.left, depend, extra);
	auto right = generate(that.right, depend, extra);
	return new JsBinary!op(left, right);
}

JsExpr generateJsDependent(alias generate, string op)(Prefix!op that, JsScope depend, Extra extra)
		if (["-", "!"].canFind(op)) {
	return new JsPrefix!op(generate(that.value, depend, extra));
}
