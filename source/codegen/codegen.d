/+
	Copyright (C) 2020  Freddy Angel Cubas "Superstar64"
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
module codegen.codegen;

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

import codegen.ast;
import jsast;

import misc.misc;

//structs are repesented as native arrays

//arrays are object with a data, start, length 
// where data may have a pointer array indexed with data.{{num}}_ptr
//pointers objects with get,and set
//functions are native js functions

JsModule generateJsModule(Module mod) {
	JsModule result = new JsModule();
	auto extra = new Extra;
	Symbol[SymbolId] symbols;

	foreach (symbol; mod.exports) {
		symbols = addDependants(symbol, symbols);
	}

	foreach (symbol; symbols) {
		extra.symbols[symbol.id] = nameSymbol(symbol);
	}

	foreach (symbol; symbols) {
		result ~= new JsVarDef(extra.symbols[symbol.id], symbol.generateSymbol(result, extra));
	}
	return result;
}

Symbol[SymbolId] addDependants(Symbol symbol, Symbol[SymbolId] symbols) {
	if (symbol.id in symbols) {
		return symbols;
	} else {
		symbols[symbol.id] = symbol;
		foreach (dependant; symbol.dependants) {
			symbols = addDependants(dependant, symbols);
		}
		return symbols;
	}
}

JsVariable nameSymbol(Symbol symbol) {
	if (symbol.strong) {
		return new JsVariable(defaultNaming(symbol.name));
	} else {
		return new JsVariable(defaultNaming(symbol.name ~ "_" ~ symbol.type.mangle));
	}
}

JsVariable symbolSubName(Pattern pattern, JsScope depend, Extra extra) {
	return dispatch!(symbolSubNameImpl, NamedPattern, TuplePattern)(pattern, depend, extra);
}

JsVariable symbolSubNameImpl(NamedPattern pattern, JsScope depend, Extra extra) {
	auto result = new JsVariable(defaultNaming(pattern.argument.name));
	extra.context.variables[pattern.argument.id] = result;
	return result;
}

JsVariable symbolSubNameImpl(TuplePattern pattern, JsScope depend, Extra extra) {
	auto result = new JsVariable(temporary);
	foreach (c, match; pattern.matches.enumerate) {
		auto sub = symbolSubName(match, depend, extra);
		depend ~= new JsVarDef(sub, indexTuple(result, c));
	}
	return result;
}

JsExpr generateSymbolImpl(FunctionLiteral that, JsScope depend, Extra extra) {
	auto argumentType = that.argument.type;
	extra.context = FunctionContext();
	JsFuncLit result = new JsFuncLit([], []);
	auto argument = symbolSubName(that.argument, result.states, extra);
	result.args = [argument];
	auto val = that.text.get.generateJs(result.states, extra);
	result.states ~= new JsReturn(val);
	return result;
}

struct FunctionContext {
	JsVariable[VarId] variables;
}

class Extra {
	FunctionContext context;

	JsVariable[SymbolId] symbols;
}

JsExpr compareInfoImpl(TypeInt that) {
	return new JsExternLit("typi_compare_vanilla");
}

JsExpr compareInfoImpl(TypeChar that) {
	return new JsExternLit("typi_compare_vanilla");
}

JsExpr compareInfoImpl(TypeBool that) {
	return new JsExternLit("typi_compare_vanilla");
}

JsExpr compareInfoImpl(TypeStruct that) {
	return new JsCall(new JsExternLit("typi_tuple_compare"), [new JsArray(that.values.map!(a => a.compareInfo).array)]);
}

JsExpr compareInfoImpl(TypeArray that) {
	return new JsCall(new JsExternLit("typi_array_compare"), [that.array.compareInfo]);
}

JsExpr compareInfoImpl(TypePointer that) {
	return new JsExternLit("typi_compare_vanilla");
}

JsExpr compareInfoImpl(TypeFunction that) {
	assert(0);
}

JsExpr indexTuple(JsExpr tuple, JsExpr index) {
	return new JsIndex(tuple, index);
}

JsExpr indexTuple(JsExpr tuple, size_t index) {
	return indexTuple(tuple, new JsIntLit(index));
}

JsExpr castInt(JsExpr expr, Type type) {
	type = type;
	if (auto i = type.castTo!TypeInt) {
		if (i.signed) {
			if (i.size == 32 || i.size == 0) {
				return new JsBinary!"|"(expr, new JsIntLit(0));
			} else {
				assert(0, "todo support size" ~ i.size.to!string);
			}
		} else {
			if (i.size == 32 || i.size == 0) {
				return new JsBinary!">>>"(expr, new JsIntLit(0));
			} else {
				assert(0, "todo support size" ~ i.size.to!string);
			}
		}
	} else {
		assert(0);
	}
}

void generateJsVarDefImpl(T)(T that, JsVariable target, JsScope depend, Extra extra) {
	depend ~= new JsVarDef(target, that.generateJs(depend, extra));
}

void generateJsVarImpl(T)(T that, JsVariable target, JsScope depend, Extra extra) {
	depend ~= new JsBinary!"="(target, that.generateJs(depend, extra));
}

JsExpr generateJsImpl(Symbol that, JsScope depend, Extra extra) {
	assert(that.id in extra.symbols, "unknown symbol " ~ that.name);
	return extra.symbols[that.id];
}

JsExpr generateJsImpl(IntLit that, JsScope depend, Extra extra) {
	return new JsIntLit(that.value.to!long);
}

JsExpr generateJsImpl(ExternJs that, JsScope depend, Extra extra) {
	return new JsExternLit(that.name);
}

JsExpr generateJsImpl(BoolLit that, JsScope depend, Extra extra) {
	if (that.yes) {
		return new JsBoolLit(true);
	} else {
		return new JsBoolLit(false);
	}
}

JsExpr generateJsImpl(CharLit that, JsScope depend, Extra extra) {
	return new JsCharLit(that.value);
}

JsExpr generateJsImpl(TupleLit that, JsScope depend, Extra extra) {
	return new JsArray(that.values.map!(a => a.generateJs(depend, extra)).array);
}

JsExpr generateJsImpl(Variable that, JsScope depend, Extra extra) {
	return extra.context.variables[that.id];
}

JsExpr generateJsImpl(If that, JsScope depend, Extra extra) {
	auto variable = new JsVariable(temporary);
	that.generateJsVarDef(variable, depend, extra);
	return variable;
}

void generateJsVarDefImpl(If that, JsVariable target, JsScope depend, Extra extra) {
	auto If = new JsIf();
	depend ~= new JsVarDef(target, new JsArray([]));
	If.cond = that.cond.generateJs(depend, extra);
	that.yes.generateJsVar(target, If.yes, extra);
	that.no.generateJsVar(target, If.no, extra);
	depend ~= If;
}

void generateJsVarImpl(If that, JsVariable target, JsScope depend, Extra extra) {
	auto If = new JsIf();
	If.cond = that.cond.generateJs(depend, extra);
	that.yes.generateJsVar(target, If.yes, extra);
	that.no.generateJsVar(target, If.no, extra);
	depend ~= If;
}

JsExpr generateJsImpl(While that, JsScope depend, Extra extra) {
	auto While = new JsWhile();
	auto cond = that.cond.generateJs(While.states, extra);

	if (While.states.length == 0) {
		While.cond = cond;
		depend ~= that.state.generateJs(While.states, extra);
	} else {
		While.cond = new JsBoolLit(true);
		While.states ~= new JsIf(new JsPrefix!"!"(cond), [new JsBreak()], []);
		depend ~= that.state.generateJs(While.states, extra);
	}
	depend ~= While;
	return new JsArray([]);
}

JsExpr getCreatePointer(Extra extra, Type type) {
	return new JsExternLit("typi_create_pointer");
}

JsExpr generateJsImpl(New that, JsScope depend, Extra extra) {
	auto value = that.value.generateJs(depend, extra);
	return new JsCall(extra.getCreatePointer(that.value.type), [value]);
}

JsExpr getNewArray(Extra extra, Type type) {
	return new JsExternLit("typi_new_array");
}

JsExpr generateJsImpl(NewArray that, JsScope depend, Extra extra) {
	auto length = that.length.generateJs(depend, extra);
	auto expression = that.value.generateJs(depend, extra);
	return new JsCall(extra.getNewArray(that.value.type), [length, expression]);
}

JsExpr generateJsImpl(CastInteger that, JsScope depend, Extra extra) {
	auto value = that.value.generateJs(depend, extra);
	return castInt(value, that.type);
}

JsExpr getArrayLength() {
	return new JsExternLit("typi_array_length");
}

JsExpr generateJsImpl(Length that, JsScope depend, Extra extra) {
	return getArrayLength;
}

JsExpr getIndexArray() {
	return new JsExternLit("typi_index_array");
}

JsExpr generateJsImpl(Index that, JsScope depend, Extra extra) {
	auto array = that.array.generateJs(depend, extra);
	auto index = that.index.generateJs(depend, extra);
	return new JsCall(getIndexArray, [array, index]);
}

JsExpr generateJsImpl(TupleIndex that, JsScope depend, Extra extra) {
	auto tuple = that.tuple.generateJs(depend, extra);
	return indexTuple(tuple, that.index);
}

JsExpr getTuplePointerForwardJs(Extra extra, Type type) {
	auto pointer = type.castTo!TypePointer;
	assert(pointer);
	auto tuple = pointer.value.castTo!TypeStruct;
	assert(tuple);
	return new JsCall(new JsExternLit("typi_tuple_address_forword"), [new JsIntLit(tuple.values.length)]);
}

JsExpr generateJsImpl(TupleIndexAddress that, JsScope depend, Extra extra) {
	auto tuple = that.tuple.generateJs(depend, extra);
	return new JsCall(extra.getTuplePointerForwardJs(that.tuple.type), [tuple, new JsIntLit(that.index)]);
}

JsExpr generateJsImpl(Call that, JsScope depend, Extra extra) {
	auto functionPointer = that.calle.generateJs(depend, extra);
	auto argument = that.argument.generateJs(depend, extra);
	return new JsCall(functionPointer, [argument]);
}

JsExpr getArraySlice() {
	return new JsExternLit("typi_array_slice");
}

JsExpr generateJsImpl(Slice that, JsScope depend, Extra extra) {
	auto array = that.array.generateJs(depend, extra);
	auto left = that.left.generateJs(depend, extra);
	auto right = that.right.generateJs(depend, extra);
	return new JsCall(getArraySlice, [array, left, right]);
}

auto getArrayLiteral(Extra extra, Type type, size_t length) {
	return new JsCall(new JsExternLit("typi_array_literal"), [new JsIntLit(length)]);
}

JsExpr generateJsImpl(StringLit that, JsScope depend, Extra extra) {
	auto internal = that.value
		.map!(a => new JsCharLit(a))
		.map!(a => a.convert!JsExpr)
		.array;
	return new JsCall(extra.getArrayLiteral(that.type.castTo!TypeArray.array, internal.length), [new JsArray(internal)]);
}

JsExpr generateJsImpl(ArrayLit that, JsScope depend, Extra extra) {
	auto internal = that.values.map!(a => a.generateJs(depend, extra)).array;
	return new JsCall(extra.getArrayLiteral(that.type.castTo!TypeArray.array, internal.length), [new JsArray(internal)]);
}

JsExpr getCompare(Extra extra, Type type) {
	return type.compareInfo;
}

JsExpr compare(JsExpr left, JsExpr right, Type type, Extra extra) {
	return new JsCall(extra.getCompare(type), [left, right]);
}

JsExpr generateJsImpl(Binary!"==" that, JsScope depend, Extra extra) {
	auto left = that.left.generateJs(depend, extra);
	auto right = that.right.generateJs(depend, extra);
	return compare(left, right, that.left.type, extra);
}

JsExpr generateJsImpl(Binary!"!=" that, JsScope depend, Extra extra) {
	auto left = that.left.generateJs(depend, extra);
	auto right = that.right.generateJs(depend, extra);
	return new JsPrefix!"!"(compare(left, right, that.left.type, extra));
}

JsExpr generateJsImpl(Binary!"~" that, JsScope depend, Extra extra) {
	assert(0, "todo implement ~");
}

JsExpr getDereferencePointer() {
	return new JsExternLit("typi_derefence_pointer");
}

JsExpr generateJsImpl(Deref that, JsScope depend, Extra extra) {
	auto value = that.value.generateJs(depend, extra);
	return new JsCall(getDereferencePointer, [value]);
}

JsExpr getArrayPointerJs(Extra extra, Type type) {
	return new JsExternLit("typi_array_address_of");
}

JsExpr generateJsImpl(IndexAddress that, JsScope depend, Extra extra) {
	auto array = that.array.generateJs(depend, extra);
	auto index = that.index.generateJs(depend, extra);
	return new JsCall(extra.getArrayPointerJs(that.type.castTo!TypePointer.value), [array, index]);
}

JsExpr generateJsImpl(Scope that, JsScope depend, Extra extra) {
	depend ~= that.pass.generateJs(depend, extra);
	return that.last.generateJs(depend, extra);
}

JsExpr generateJsImpl(VariableDef that, JsScope depend, Extra extra) {
	JsScope temp = new JsScope;
	auto variable = symbolSubName(that.variable, temp, extra);
	that.value.generateJsVarDef(variable, depend, extra);
	//todo: clean this
	foreach (state; temp) {
		depend ~= temp;
	}
	return that.last.generateJs(depend, extra);
}

JsExpr getAssignPointer() {
	return new JsExternLit("typi_pointer_assign");
}

JsExpr generateJsImpl(Assign that, JsScope depend, Extra extra) {
	auto target = that.left.generateJs(depend, extra);
	auto source = that.right.generateJs(depend, extra);
	return new JsCall(getAssignPointer(), [target, source]);
}

JsExpr generateJsImpl(string op)(Binary!op that, JsScope depend, Extra extra) if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = that.left.generateJs(depend, extra);
	auto right = that.right.generateJs(depend, extra);
	return castInt(new JsBinary!op(left, right), that.type);
}

JsExpr generateJsImpl(string op)(Binary!op that, JsScope depend, Extra extra) if (["<=", ">=", "<", ">", "&&", "||"].canFind(op)) {
	auto left = that.left.generateJs(depend, extra);
	auto right = that.right.generateJs(depend, extra);
	return new JsBinary!op(left, right);
}

JsExpr generateJsImpl(string op)(Prefix!op that, JsScope depend, Extra extra) if (["-", "!"].canFind(op)) {
	return new JsPrefix!op(that.value.generateJs(depend, extra));
}
