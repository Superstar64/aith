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

import misc.container;
import misc.misc;

import semantic.ast;
import jsast;

JsModule generateJsModule(Module mod) {
	JsModule result = new JsModule();
	auto extra = new Extra;
	Dictonary!(Tuple!(SymbolId, TypeHash), Symbol) symbols;

	foreach (candidate; mod.orderedAliases) {
		if (auto symbol = candidate.get.get.castTo!Symbol) {
			if (symbol.type.freeVariables.length == 0) {
				symbols = addDependants(symbol, symbols);
			}
		}
	}

	foreach (key, symbol; symbols.range) {
		extra.symbols[key] = nameSymbol(symbol);
	}

	foreach (key, symbol; symbols.range) {
		result ~= new JsVarDef(extra.symbols[key], symbol.generateSymbol(result, extra), true);
	}
	return result;
}

Dictonary!(Tuple!(SymbolId, TypeHash), Symbol) addDependants(Symbol symbol, Dictonary!(Tuple!(SymbolId, TypeHash), Symbol) symbols) {
	if (tuple(symbol.id, symbol.type.typeHash) in symbols) {
		return symbols;
	} else {
		symbols[tuple(symbol.id, symbol.type.typeHash)] = symbol;
		foreach (dependant; symbol.dependants.byValue) {
			symbols = addDependants(dependant, symbols);
		}
		return symbols;
	}
}

JsVariable nameSymbol(Symbol symbol) {
	if (symbol.linkage == Linkage.strong) {
		return new JsVariable(defaultNaming(symbol.name));
	} else {
		return new JsVariable(defaultNaming(symbol.name ~ "_" ~ symbol.type.mangle));
	}
}

JsPattern generatePatternMatchImpl(NamedPattern that, Extra extra) {
	auto result = new JsVariable(defaultNaming(that.argument.name));
	extra.context.variables[that.argument.id] = result;
	return result;
}

JsPattern generatePatternMatchImpl(TuplePattern that, Extra extra) {
	auto matches = that.matches.map!(a => a.generatePatternMatch(extra)).array;
	return new JsArrayPattern(matches);
}

JsExpr generateSymbolImpl(FunctionLiteral that, JsScope depend, Extra extra) {
	extra.context = FunctionContext();

	auto pattern = that.argument.generatePatternMatch(extra);
	auto result = new JsLambda([pattern], []);

	auto val = that.text.get.generateJs(result.states, extra);
	result.states ~= new JsReturn(val);
	return result;
}

struct FunctionContext {
	Dictonary!(VarId, JsVariable) variables;
}

class Extra {
	FunctionContext context;
	Dictonary!(Tuple!(SymbolId, TypeHash), JsVariable) symbols;
	JsExpr requestExtern(string name)() {
		return new JsExternLit(name);
	}
}

JsExpr compareInfoImpl(TypeInt that, Extra extra) {
	return extra.requestExtern!"typi_compare_vanilla";
}

JsExpr compareInfoImpl(TypeChar that, Extra extra) {
	return extra.requestExtern!"typi_compare_vanilla";
}

JsExpr compareInfoImpl(TypeBool that, Extra extra) {
	return extra.requestExtern!"typi_compare_vanilla";
}

JsExpr compareInfoImpl(TypeStruct that, Extra extra) {
	return new JsCall(extra.requestExtern!"typi_tuple_compare", [new JsArray(that.values.map!(a => a.compareInfo(extra)).array)]);
}

JsExpr compareInfoImpl(TypeArray that, Extra extra) {
	return new JsCall(extra.requestExtern!"typi_array_compare", [that.array.compareInfo(extra)]);
}

JsExpr compareInfoImpl(TypePointer that, Extra extra) {
	return extra.requestExtern!"typi_compare_vanilla";
}

JsExpr compareInfoImpl(TypeOwnPointer that, Extra extra) {
	assert(0);
}

JsExpr compareInfoImpl(TypeOwnArray that, Extra extra) {
	assert(0);
}

JsExpr compareInfoImpl(TypeFunction that, Extra extra) {
	assert(0);
}

JsExpr compareInfoImpl(TypeWorld that, Extra extra) {
	assert(0);
}

string mangleImpl(TypeBool) {
	return "boolean";
}

string mangleImpl(TypeChar) {
	return "character";
}

string mangleImpl(TypeInt that) {
	with (that)
		return (signed ? "integer" : "natural") ~ size.to!string;
}

string mangleImpl(TypeStruct that) {
	with (that) {
		if (values.length == 0) {
			return "void";
		}
		return "tuple_of_" ~ values[0 .. $ - 1].map!(a => a.mangle ~ "_and_")
			.joiner
			.to!string ~ values[$ - 1].mangle ~ "_end";
	}
}

string mangleImpl(TypeArray that) {
	with (that)
		return array.mangle ~ "_array";
}

string mangleImpl(TypeFunction that) {
	with (that)
		return "function_of_" ~ argument.mangle ~ "_to_" ~ result.mangle ~ "_end";
}

string mangleImpl(TypePointer that) {
	with (that)
		return value.mangle ~ "_pointer";
}

string mangleImpl(TypeOwnPointer that) {
	with (that)
		return value.mangle ~ "_own_pointer";
}

string mangleImpl(TypeOwnArray that) {
	with (that)
		return array.mangle ~ "_own_pointer";
}

string mangleImpl(TypeWorld that) {
	with (that)
		return "world";
}

JsExpr generateJsImpl(Symbol that, JsScope depend, Extra extra) {
	assert(tuple(that.id, that.type.typeHash) in extra.symbols, "unknown symbol " ~ that.name);
	return extra.symbols[tuple(that.id, that.type.typeHash)];
}

JsExpr generateJsImpl(IntLit that, JsScope depend, Extra extra) {
	return new JsIntLit(that.value.to!long);
}

JsExpr generateJsImpl(ExternJs that, JsScope depend, Extra extra) {
	return new JsExternLit(that.name);
}

JsExpr generateJsImpl(BoolLit that, JsScope depend, Extra extra) {
	return new JsBoolLit(that.yes);
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
	auto If = new JsIf();
	depend ~= new JsVarDef(variable, null, false);
	If.cond = that.cond.generateJs(depend, extra);
	If.yes ~= new JsBinary!"="(variable, that.yes.generateJs(If.yes, extra));
	If.no ~= new JsBinary!"="(variable, that.no.generateJs(If.no, extra));
	depend ~= If;
	return variable;
}

JsExpr generateJsImpl(Desugar!"new" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_create_pointer";
}

JsExpr generateJsImpl(Desugar!"borrow" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_borrow_pointer";
}

JsExpr generateJsImpl(Desugar!"delete" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_delete_pointer";
}

JsExpr generateJsImpl(Desugar!"new array" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_new_array";
}

JsExpr generateJsImpl(Desugar!"borrow array" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_borrow_array";
}

JsExpr generateJsImpl(Desugar!"delete array" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_delete_array";
}

JsExpr generateJsImpl(CastInteger that, JsScope depend, Extra extra) {
	return applyNumber(applyNumber(extra.requestExtern!"typi_cast_integer", that.contextWanted), that.contextInput);
}

JsExpr generateJsImpl(Desugar!"length" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_array_length";
}

JsExpr generateJsImpl(Desugar!"index" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_index_array";
}

JsExpr generateJsImpl(TupleIndex that, JsScope depend, Extra extra) {
	return new JsCall(extra.requestExtern!"typi_index_tuple", [new JsIntLit(that.index)]);
}

JsExpr getTuplePointerForwardJs(Extra extra, Type type, int index) {
	auto tuple = type.castTo!TypeStruct;
	assert(tuple);
	return new JsCall(extra.requestExtern!"typi_tuple_address_forword", [new JsIntLit(index), new JsIntLit(tuple.values.length)]);
}

JsExpr generateJsImpl(TupleIndexAddress that, JsScope depend, Extra extra) {
	return extra.getTuplePointerForwardJs(that.context, that.index);
}

JsExpr generateJsImpl(Call that, JsScope depend, Extra extra) {
	auto functionPointer = that.calle.generateJs(depend, extra);
	auto argument = that.argument.generateJs(depend, extra);
	return new JsCall(functionPointer, [argument]);
}

JsExpr generateJsImpl(Desugar!"slice" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_array_slice";
}

auto getArrayLiteral(Extra extra, size_t length) {
	return new JsCall(extra.requestExtern!"typi_array_literal", [new JsIntLit(length)]);
}

JsExpr generateJsImpl(StringLit that, JsScope depend, Extra extra) {
	auto internal = that.value
		.map!(a => new JsCharLit(a))
		.map!(a => a.convert!JsExpr)
		.array;
	return new JsCall(extra.getArrayLiteral(internal.length), [new JsArray(internal)]);
}

JsExpr generateJsImpl(ArrayLit that, JsScope depend, Extra extra) {
	auto internal = that.values.map!(a => a.generateJs(depend, extra)).array;
	return new JsCall(extra.getArrayLiteral(internal.length), [new JsArray(internal)]);
}

JsExpr generateJsImpl(DesugarContext!"equal" that, JsScope depend, Extra extra) {
	return that.context.compareInfo(extra);
}

JsExpr generateJsImpl(DesugarContext!"not equal" that, JsScope depend, Extra extra) {
	return new JsCall(extra.requestExtern!"typi_compare_not", [that.context.compareInfo(extra)]);
}

JsExpr generateJsImpl(Desugar!"derefence" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_derefence_pointer";
}

JsExpr generateJsImpl(Desugar!"index address" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_array_address_of";
}

JsExpr generateJsImpl(VariableDefinition that, JsScope depend, Extra extra) {
	depend ~= new JsVarDef(that.variable.generatePatternMatch(extra), that.value.generateJs(depend, extra), true);
	return that.last.generateJs(depend, extra);
}

JsExpr generateJsImpl(Desugar!"assign" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_pointer_assign";
}

JsExpr applyNumber(JsExpr builtin, Type type) {
	auto number = type.castTo!TypeInt;
	assert(number);
	return new JsCall(builtin, [new JsIntLit(number.size), new JsBoolLit(number.signed)]);
}

JsExpr generateJsImpl(DesugarContext!"multiply" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_multiply", that.context);
}

JsExpr generateJsImpl(DesugarContext!"divide" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_divide", that.context);
}

JsExpr generateJsImpl(DesugarContext!"modulus" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_modulus", that.context);
}

JsExpr generateJsImpl(DesugarContext!"add" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_add", that.context);
}

JsExpr generateJsImpl(DesugarContext!"subtract" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_subtract", that.context);
}

JsExpr generateJsImpl(DesugarContext!"less equal" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_lessthan_equal", that.context);
}

JsExpr generateJsImpl(DesugarContext!"greater equal" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_greater_equal", that.context);
}

JsExpr generateJsImpl(DesugarContext!"less" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_lessthan", that.context);
}

JsExpr generateJsImpl(DesugarContext!"greater" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_greater", that.context);
}

JsExpr generateJsImpl(Desugar!"and" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_and";
}

JsExpr generateJsImpl(Desugar!"or" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_or";
}

JsExpr generateJsImpl(DesugarContext!"negate" that, JsScope depend, Extra extra) {
	return applyNumber(extra.requestExtern!"typi_negate", that.context);
}

JsExpr generateJsImpl(Desugar!"not" that, JsScope depend, Extra extra) {
	return extra.requestExtern!"typi_not";
}
