/+
	Copyright (C) 2020  Freddy Angel Cubas "Superstar64"
	This file is part of Aith.

	Aith is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation version 3 of the License.

	Aith is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with Aith.  If not, see <http://www.gnu.org/licenses/>.
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

import app : knownSymbols;

JsModule generateJsModule(Module mod) {
	JsModule result = new JsModule();
	auto extra = new Extra;

	foreach (id; mod.exports.map!(a => a())) {
		extra.symbols.insert(id, new JsVariable(defaultNaming(knownSymbols[id].name)));
	}

	foreach (id; mod.exports.map!(a => a())) {
		extra.variables.clear;
		extra.dictonaries.clear;

		JsVariable[] dictonariesOrdered;
		foreach (dictonary; knownSymbols[id].dictonaries) {
			auto variable = dictonary[0];
			auto argument = new JsVariable(temporary);
			dictonariesOrdered ~= argument;
			extra.dictonaries.insert(tuple(variable.id, dictonary[1].id), argument);
		}
		auto internal = knownSymbols[id].source.generateJs(result, extra);
		if (dictonariesOrdered.length > 0) {
			result ~= new JsVarDef(extra.symbols[id], new JsLambda(dictonariesOrdered.map!(convert!JsPattern).array, [new JsReturn(internal)]), true);
		} else {
			result ~= new JsVarDef(extra.symbols[id], internal, true);
		}
	}
	return result;
}

class Extra {
	OwnerDictonary!(VariableId, JsVariable) variables;
	OwnerDictonary!(Tuple!(TypeVariableId, PredicateId), JsVariable) dictonaries;
	OwnerDictonary!(SymbolId, JsVariable) symbols;
}

JsExpr external(string name) {
	return new JsExternLit(name);
}

JsPattern generatePatternMatchImpl(NamedPattern that, Extra extra) {
	auto result = new JsVariable(defaultNaming(that.name));
	assert(!(that.id in extra.variables));
	extra.variables.insert(that.id, result);
	return result;
}

JsPattern generatePatternMatchImpl(TuplePattern that, Extra extra) {
	auto matches = that.matches.map!(a => a.generatePatternMatch(extra)).array;
	return new JsArrayPattern(matches);
}

void removeBindings(Pattern pattern, Extra extra) {
	auto bindings = pattern.orderedBindings;
	foreach (binding; bindings) {
		extra.variables.remove(binding[0].id);
	}
}

JsExpr generateJsImpl(MacroFunctionLiteral that, JsScope depend, Extra extra) {
	auto variable = new JsVariable(defaultNaming(that.argument.name));
	assert(!(that.argument.id in extra.variables));
	extra.variables.insert(that.argument.id, variable);
	auto result = new JsLambda([variable], []);

	auto val = that.text.generateJs(result.states, extra);
	result.states ~= new JsReturn(val);
	extra.variables.remove(that.argument.id);
	return result;
}

JsExpr generateJsImpl(Call that, JsScope depend, Extra extra) {
	auto functionPointer = that.calle.generateJs(depend, extra);
	auto argument = that.argument.generateJs(depend, extra);
	return new JsCall(functionPointer, [argument]);
}

JsExpr generateJsImpl(MacroCall that, JsScope depend, Extra extra) {
	assert(0);
}

JsExpr generateJsImpl(SymbolForwardReference that, JsScope depend, Extra extra) {
	assert(0);
}

JsExpr infoImpl(T)(T that, PredicateTypeMatch predicate, JsScope depend, Extra extra) if (!is(T : TypeVariable)) {
	return predicate.pattern.typeInfo(that, depend, extra);
}

JsExpr infoImpl(P : Predicate)(TypeVariable that, P predicate, JsScope depend, Extra extra) {
	return extra.dictonaries[tuple(that.id, predicate.id)];
}

JsExpr infoImpl(P : TypeMatch)(TypeVariable that, P predicate, JsScope depend, Extra extra) {
	assert(0);
}

JsExpr infoImpl(Type that, TypeMatchCustom custom, JsScope depend, Extra extra) {
	return custom.match.generateJs(depend, extra);
}

JsExpr infoImpl(Type that, TypeMatchOr or, JsScope depend, Extra extra) {
	if (or.left.match(that)) {
		return or.left.typeInfo(that, depend, extra);
	} else {
		assert(or.right.match(that));
		return or.right.typeInfo(that, depend, extra);
	}
}

JsExpr infoImpl(TypeInt that, TypeMatchEqual, JsScope depend, Extra extra) {
	return "aith_compare_vanilla".external;
}

JsExpr infoImpl(TypeChar that, TypeMatchEqual, JsScope depend, Extra extra) {
	return "aith_compare_vanilla".external;
}

JsExpr infoImpl(TypeBool that, TypeMatchEqual, JsScope depend, Extra extra) {
	return "aith_compare_vanilla".external;
}

import semantic.astimpl : predicateEqual;

JsExpr infoImpl(TypeStruct that, TypeMatchEqual, JsScope depend, Extra extra) {
	return new JsCall("aith_tuple_compare".external, [new JsArray(that.values.map!(a => predicateEqual.typeInfo(a, depend, extra)).array)]);
}

JsExpr infoImpl(TypeArray that, TypeMatchEqual, JsScope depend, Extra extra) {
	return new JsCall("aith_array_compare".external, [predicateEqual.typeInfo(that.value, depend, extra)]);
}

JsExpr infoImpl(TypePointer that, TypeMatchEqual, JsScope depend, Extra extra) {
	return "aith_compare_vanilla".external;
}

JsExpr infoImpl(T)(T, TypeMatchEqual, JsScope depend, Extra extra) if (staticIndexOf!(T, TypeFunction, TypeWorld, TypeOwnArray, TypeOwnPointer, TypeMacro, TypeVariableRigid) != -1) {
	assert(0);
}

JsExpr infoImpl(TypeInt that, TypeMatchNumber predicate, JsScope depend, Extra extra) {
	return external("aith_number_" ~ (that.signed ? "integer" : "natural") ~ that.size.to!string);
}

JsExpr infoImpl(T)(T, TypeMatchNumber, JsScope depend, Extra extra) if (!is(T : TypeInt)) {
	assert(0);
}

JsExpr infoImpl(TypeStruct that, PredicateTuple predicate, JsScope depend, Extra extra) {
	return new JsCall("aith_has_tuple".external, [new JsIntLit(predicate.index).convert!JsExpr, new JsIntLit(that.values.length).convert!JsExpr]);
}

JsExpr infoImpl(T)(T, PredicateTuple, JsScope depend, Extra extra) if (!is(T : TypeStruct)) {
	assert(0);
}

JsExpr infoImpl(T)(T, TypeMatchUnrestricted, JsScope depend, Extra extra) {
	return new JsExternLit("undefined");
}

JsExpr generateJsImpl(SymbolReference that, JsScope depend, Extra extra) {
	assert(that.id in extra.symbols, "unknown symbol " ~ that.name);
	JsExpr[] dictonaries = that.dictonaries.map!(a => a[1].typeInfo(a[0], depend, extra)).array;
	if (dictonaries.length > 0) {
		return new JsCall(extra.symbols[that.id], dictonaries);
	} else {
		return extra.symbols[that.id];
	}
}

JsExpr generateJsImpl(ExternJs that, JsScope depend, Extra extra) {
	JsExpr[] dictonaries = that.dictonaries.map!(a => a[1].typeInfo(a[0], depend, extra)).array;
	if (dictonaries.length > 0) {
		return new JsCall(new JsExternLit(that.name), dictonaries);
	} else {
		return new JsExternLit(that.name);
	}
}

JsExpr generateJsImpl(Requirement that, JsScope depend, Extra extra) {
	return that.requirement.typeInfo(that.context, depend, extra);
}

JsExpr generateJsImpl(IntLit that, JsScope depend, Extra extra) {
	return new JsIntLit(that.value.to!long);
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
	assert(that.id in extra.variables, "Unscoped variable: " ~ that.name);
	return extra.variables[that.id];
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

auto getArrayLiteral(Extra extra, size_t length) {
	return new JsCall("aith_array_literal".external, [new JsIntLit(length)]);
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

JsExpr generateJsImpl(VariableDefinition that, JsScope depend, Extra extra) {
	auto value = that.value.generateJs(depend, extra);
	depend ~= new JsVarDef(that.variable.generatePatternMatch(extra), value, true);
	auto result = that.last.generateJs(depend, extra);
	that.variable.removeBindings(extra);
	return result;
}
