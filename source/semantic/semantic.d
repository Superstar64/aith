/+
	Copyright (C) 2015-2017  Freddy Angel Cubas "Superstar64"
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
module semantic.semantic;
import std.algorithm;
import std.array;
import std.bigint;
import std.conv;
import std.file;
import std.meta;
import std.range;
import std.typecons;

import genericast;

static import Parser = parser.ast;
import semantic.astimpl;

import misc.nonstrict;
import misc.position;
import misc.container;
import misc.misc;

class Context {
	Module mod;

	Parser.ModuleVarDef preassignSymbol;
	CompileTimeExpression preassignExpression; //nullable

	Expression[string] passdownGlobals;
	Position[TypeVariableId] freshVariables;
	Equivalence[] typeChecks;

	Binding[string] locals;

	Context previous;
	bool passdown;

	void typeCheck(Type left, Type right, Position position) {
		typeChecks ~= Equivalence(left, right, position);
	}

	this(Module mod, Parser.ModuleVarDef preassignSymbol, Context previous) {
		this.mod = mod;
		this.preassignSymbol = preassignSymbol;
		this.previous = previous;
	}

	void bindVariable(Binding variable, Position position) {
		if (variable.name in locals) {
			error("duplicate name", position);
		}
		locals[variable.name] = variable;
	}

	void pass() {
		assert(!!previous);
		assert(passdown);
		foreach (name, variable; passdownGlobals) {
			previous.passdownGlobals[name] = variable;
		}

		foreach (variable, position; freshVariables) {
			previous.freshVariables[variable] = position;
		}

		foreach (equation; typeChecks) {
			previous.typeChecks ~= equation;
		}
	}
}

ContextRange range(Context context) {
	return ContextRange(context);
}

struct ContextRange {
	Context item;
	bool empty() {
		return item is null;
	}

	Context front() {
		return item;
	}

	void popFront() {
		item = item.previous;
	}
}

CompileTimeExpression search(Context context, string name, Position position) {
	if (name in context.locals) {
		return context.locals[name];
	}
	return searchGlobal(context.mod, context, name, position);
}

CompileTimeExpression searchGlobal(Module mod, Context context, string name, Position position) {
	if (name in mod.aliases) {
		return mod.aliases[name].element;
	} else if (name in mod.rawSymbols) {
		auto symbol = mod.rawSymbols[name];
		auto recursive = context.range.find!(a => a.preassignSymbol is symbol);
		if (recursive.empty) {
			return semanticGlobal(symbol, mod, context);
		} else {
			Context original = recursive.front;
			assert(original.preassignSymbol is symbol);
			check(!!original.preassignExpression, "Illegal recursion", position);
			context.range
				.until!(a => a.preassignSymbol is symbol)
				.each!(frame => frame.passdown = true);
			return original.preassignExpression;
		}
	} else {
		return null;
	}
}

Module lazyCreateModule(Parser.Module parser) {
	auto mod = new Module();
	foreach (symbol; parser.symbols) {
		check(!(symbol.name in mod.rawSymbols), "Symbol already exists", symbol.position);
		mod.rawSymbols[symbol.name] = symbol;
		mod.rawSymbolsOrdered ~= symbol;
	}
	return mod;
}

void processModule(Module mod) {
	foreach (symbol; mod.rawSymbolsOrdered) {
		if (symbol.name in mod.aliases) {
			continue;
		}
		semanticGlobal(symbol, mod, null);
	}
}

TypeVariable freshTypeVariable(Context context, Position position, Predicate[] constraints = null, string name = null, RigidVariable[RigidContext] rigidity = null) {
	auto id = make!TypeVariableId(name);
	context.freshVariables[id] = position;
	Predicate[PredicateId] constraintsMap;
	foreach (constraint; constraints) {
		constraintsMap[constraint.id] = constraint;
	}
	auto qualified = make!TypeVariable(id, constraintsMap, rigidity);
	return qualified;
}

CompileTimeExpression semanticGlobal(Parser.ModuleVarDef symbol, Module mod, Context previous) {
	foreach (frame; previous.range) {
		assert(!(symbol is frame.preassignSymbol));
	}

	Context context = new Context(mod, symbol, previous);
	auto rigidContext = make!RigidContext(symbol.name);
	foreach (polymorphicVariable; symbol.polymorphicVariables) {
		auto rigidity = [rigidContext : make!RigidVariable(polymorphicVariable)];
		auto variable = freshTypeVariable(context, symbol.position, null, polymorphicVariable, rigidity);
		context.bindVariable(variable, symbol.position);
	}
	Type type;
	if (symbol.explicitType) {
		type = symbol.explicitType.semanticType(context);
	}

	// for recursive ast nodes that may reference them selfs
	void preassign(CompileTimeExpression expression) {
		context.preassignExpression = expression;
	}

	auto expression = semanticGlobalDispatch(symbol.value, symbol.name, type, context, &preassign);

	if (auto expression1 = expression.castTo!Expression) {
		context.passdownGlobals[symbol.name] = expression1;
	}
	if (context.passdown) {
		context.pass;
	} else {
		auto substitution = typeMatch(context.typeChecks);
		foreach (name, expression1; context.passdownGlobals) {

			foreach (variable, position; context.freshVariables) {
				auto free = (variable in substitution) ? substitution[variable].freeVariables.mapValues!(a => tuple()) : null;
				if (!isSubSet(free, expression1.type.specialize(substitution).freeVariables.mapValues!(a => tuple()))) {
					error("Unable to infer type variable", position);
				}
			}

			expression1 = expression1.specialize(substitution);
			//remove rigidity
			auto fresh = expression1.type.freshFlexibleSubstitution;
			expression1 = expression1.specialize(fresh);

			mod.aliases[name] = ModuleAlias(expression1);
			if (auto expression2 = expression1.castTo!Symbol) {
				if (expression2.strong && expression2.type.freeVariables.length == 0) {
					mod.exports[symbol.name] = expression2;
				}
			}
			expression = expression1;
		}
	}
	// ugly hack
	if (!expression.castTo!Expression) {
		mod.aliases[symbol.name] = ModuleAlias(expression);
	}
	return expression;
}

CompileTimeExpression semanticGlobalDispatch(Parser.Expression that, string name, /* nullable */ Type type, Context context, void delegate(CompileTimeExpression) preassign) {
	return dispatch!(semanticGlobalImpl, Parser.Variable, Parser.TypeTuple, Parser.Index, Parser.TupleIndex, Parser.TupleIndexAddress, Parser.IndexAddress, Parser.Call, Parser.Length, Parser.TypeBool, Parser.TypeChar, Parser.TypeInt, Parser.Import, Parser.IntLit, Parser.CharLit, Parser.BoolLit, Parser.TupleLit, Parser.If, Parser.While, Parser.New, Parser.NewArray, Parser.Cast, Parser.Infer, Parser.Slice, Parser.Assign, Parser.VariableDef, Parser.FuncLit, Parser.StringLit, Parser.ArrayLit, Parser.ExternJs, Parser.Binary!"*", Parser.Binary!"/", Parser.Binary!"%", Parser.Binary!"+", Parser.Binary!"-", Parser.Binary!"~", Parser.Binary!"==", Parser.Binary!"!=", Parser.Binary!"<=", Parser.Binary!">=", Parser.Binary!"<", Parser.Binary!">", Parser.Binary!"&&", Parser.Binary!"||", Parser.Prefix!"-", Parser.Prefix!"*", Parser.Prefix!"!", Parser.Postfix!"(*)", Parser.Postfix!"[*]", Parser.Binary!"->", Parser.UseSymbol)(that, name, type, context, preassign);
}

CompileTimeExpression semanticGlobalImpl(Parser.FuncLit that, string name, Type annotation, Context context, void delegate(CompileTimeExpression) preassign) {
	auto argument = semanticPattern(that.argument, context);
	auto returnType = context.freshTypeVariable(that.position);
	auto type = make!TypeFunction(returnType, argument.type);
	if (annotation) {
		context.typeCheck(type, annotation, that.position);
	}
	// has side effects
	Expression get() {
		return semanticExpression(that.text, context);
	}

	auto result = make!FunctionLiteral(type, name, !!annotation, new SymbolId, argument, defer(&get));
	preassign(result);
	result.text.eval; // required to collect unification constraints
	context.typeCheck(result.text.get.type, returnType, that.position);
	return result;
}

CompileTimeExpression semanticGlobalImpl(T)(T that, string name, Type annotation, Context context, void delegate(CompileTimeExpression) preassign) {
	auto expression = semanticMain(that, context);
	if (annotation) {
		// todo fix this
		auto runtime = expression.assumeExpression(that.position);
		context.typeCheck(runtime.type, annotation, that.position);
	}
	return expression;
}

Type assumeType(CompileTimeExpression value, Position position, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!Type, "Expected type", position, file, line);
	return value.castTo!Type;
}

Expression assumeExpression(CompileTimeExpression value, Position position, string file = __FILE__, int line = __LINE__) {
	auto result = value.castTo!Expression;
	check(result, "Expected polymorphic value", position, file, line);

	return result;
}

Type semanticType(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeType(semanticMain(that, context), that.position, file, line);
}

Expression semanticExpression(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeExpression(semanticMain(that, context), that.position, file, line);
}

auto semanticMain(Parser.Expression that, Context context) {
	auto result = semanticImplDispatch(that, context);
	return result;
}

CompileTimeExpression semanticImplDispatch(Parser.Expression that, Context context) {
	return dispatch!(semanticImpl, Parser.Variable, Parser.TypeTuple, Parser.Index, Parser.IndexAddress, Parser.TupleIndex, Parser.TupleIndexAddress, Parser.Call, Parser.Length, Parser.TypeBool, Parser.TypeChar, Parser.TypeInt, Parser.Import, Parser.IntLit, Parser.CharLit, Parser.BoolLit, Parser.TupleLit, Parser.If, Parser.While, Parser.New, Parser.NewArray, Parser.Cast, Parser.Infer, Parser.Slice, Parser.Assign, Parser.VariableDef, Parser.FuncLit, Parser.StringLit, Parser.ArrayLit, Parser.ExternJs, Parser.Binary!"*", Parser.Binary!"/", Parser.Binary!"%", Parser.Binary!"+", Parser.Binary!"-", Parser.Binary!"~", Parser.Binary!"==", Parser.Binary!"!=", Parser.Binary!"<=", Parser.Binary!">=", Parser.Binary!"<", Parser.Binary!">", Parser.Binary!"&&", Parser.Binary!"||", Parser.Prefix!"-", Parser.Prefix!"*", Parser.Prefix!"!", Parser.Postfix!"(*)", Parser.Postfix!"[*]", Parser.Binary!"->", Parser.UseSymbol)(that, context);
}

CompileTimeExpression semanticImpl(Parser.Variable that, Context context) {
	auto variable = context.search(that.name, that.position);
	check(!(variable is null), "Undefined variable", that.position);
	return variable;
}

CompileTimeExpression semanticImpl(Parser.Import that, Context context) {
	return make!Import(that.mod);
}

CompileTimeExpression semanticImpl(Parser.UseSymbol that, Context context) {
	auto value = semanticMain(that.value, context);
	auto mod = value.castTo!Import.mod;
	check(mod, "scope resolution expect a module", that.position);
	auto variable = mod.searchGlobal(context, that.index, that.position);
	check(!(variable is null), "Undefined variable", that.position);
	return variable;
}

CompileTimeExpression semanticImpl(Parser.TypeTuple that, Context context) {
	auto types = that.values.map!(a => semanticType(a, context)).array;
	return make!TypeStruct(types);
}

CompileTimeExpression semanticImpl(Parser.Length that, Context context) {
	auto variable = context.freshTypeVariable(that.position);
	auto type = make!TypeFunction(make!TypeInt(0, false), make!TypeArray(variable));
	return make!Length(type);
}

CompileTimeExpression semanticImpl(Parser.TypeBool that, Context context) {
	return make!TypeBool();
}

CompileTimeExpression semanticImpl(Parser.TypeChar that, Context context) {
	return make!TypeChar();
}

void checkIntSize(int size, Position position) {
	check(size == 0 || size == 8 || size == 16 || size == 32, "Bad TypeInt Size", position);
}

CompileTimeExpression semanticImpl(Parser.TypeInt that, Context context) {
	checkIntSize(that.size, that.position);
	return make!TypeInt(that.size, that.signed);
}

CompileTimeExpression semanticImpl(Parser.Postfix!"(*)" that, Context context) {
	auto value = semanticType(that.value, context);
	return make!TypePointer(value);
}

CompileTimeExpression semanticImpl(Parser.Postfix!"[*]" that, Context context) {
	auto value = semanticType(that.value, context);
	return make!TypeArray(value);
}

CompileTimeExpression semanticImpl(Parser.IntLit that, Context context) {
	auto variable = context.freshTypeVariable(that.position, [make!PredicateNumber.convert!Predicate]);
	return make!IntLit(variable, that.value);
}

CompileTimeExpression semanticImpl(Parser.CharLit that, Context context) {
	return make!CharLit(make!TypeChar(), that.value);
}

CompileTimeExpression semanticImpl(Parser.BoolLit that, Context context) {
	return make!BoolLit(make!TypeBool(), that.yes);
}

CompileTimeExpression semanticImpl(Parser.TupleLit that, Context context) {
	auto values = that.values.map!(a => semanticExpression(a, context)).array;
	return make!TupleLit(make!TypeStruct(values.map!(a => a.type).array), values);
}

CompileTimeExpression semanticImpl(Parser.If that, Context context) {
	auto cond = semanticExpression(that.cond, context);
	auto yes = semanticExpression(that.yes, context);
	auto no = semanticExpression(that.no, context);
	context.typeCheck(cond.type, make!TypeBool(), that.cond.position);
	context.typeCheck(yes.type, no.type, that.position);
	return make!If(yes.type, cond, yes, no);
}

CompileTimeExpression semanticImpl(Parser.While that, Context context) {
	auto cond = semanticExpression(that.cond, context);
	auto state = semanticExpression(that.state, context);
	context.typeCheck(cond.type, make!TypeBool(), that.cond.position);
	return make!While(make!TypeStruct(emptyArray!Type), cond, state);
}

CompileTimeExpression semanticImpl(Parser.New that, Context context) {
	auto value = semanticExpression(that.value, context);
	return make!New(make!TypePointer(value.type), value);
}

CompileTimeExpression semanticImpl(Parser.NewArray that, Context context) {
	auto length = semanticExpression(that.length, context);
	auto value = semanticExpression(that.value, context);
	context.typeCheck(length.type, make!TypeInt(0, false), that.length.position);
	return make!NewArray(make!TypeArray(value.type), length, value);
}

CompileTimeExpression semanticImpl(Parser.Cast that, Context context) {
	auto wanted = semanticType(that.type, context);
	auto value = semanticExpression(that.value, context);
	auto expected = context.freshTypeVariable(that.position, [make!PredicateNumber.convert!Predicate]);
	context.typeCheck(value.type, expected, that.value.position);

	auto valid = context.freshTypeVariable(that.position, [make!PredicateNumber.convert!Predicate]);
	context.typeCheck(wanted, valid, that.position);

	return make!CastInteger(wanted, value);
}

CompileTimeExpression semanticImpl(Parser.Infer that, Context context) {
	auto argumentType = semanticType(that.type, context);
	auto value = semanticExpression(that.value, context);
	context.typeCheck(argumentType, value.type, that.position);
	return value;
}

CompileTimeExpression semanticImpl(Parser.Index that, Context context) {
	auto array = semanticExpression(that.array, context);
	auto index = semanticExpression(that.index, context);
	auto variable = context.freshTypeVariable(that.position);
	context.typeCheck(array.type, make!TypeArray(variable), that.array.position);
	context.typeCheck(index.type, make!TypeInt(0, false), that.index.position);
	return make!Index(variable, array, index);
}

CompileTimeExpression semanticImpl(Parser.IndexAddress that, Context context) {
	auto array = semanticExpression(that.array, context);
	auto index = semanticExpression(that.index, context);
	auto variable = context.freshTypeVariable(that.position);
	context.typeCheck(array.type, make!TypeArray(variable), that.array.position);
	context.typeCheck(index.type, make!TypeInt(0, false), that.index.position);
	return make!IndexAddress(make!TypePointer(variable), array, index);
}

CompileTimeExpression semanticImpl(Parser.TupleIndex that, Context context) {
	auto tuple = semanticExpression(that.tuple, context);
	auto index = that.index;

	auto type = context.freshTypeVariable(that.position);
	auto tupletype = context.freshTypeVariable(that.position, [make!PredicateTuple(that.index, type).convert!Predicate]);
	context.typeCheck(tuple.type, tupletype, that.position);
	return make!TupleIndex(type, tuple, index);
}

CompileTimeExpression semanticImpl(Parser.TupleIndexAddress that, Context context) {
	auto tuple = semanticExpression(that.tuple, context);
	auto index = that.index;
	auto variable = context.freshTypeVariable(that.position);
	auto tupletype = make!TypePointer(context.freshTypeVariable(that.position, [make!PredicateTuple(that.index, variable).convert!Predicate]));
	context.typeCheck(tuple.type, tupletype, that.position);
	return make!TupleIndexAddress(make!TypePointer(variable), tuple, index);
}

CompileTimeExpression semanticImpl(Parser.Call that, Context context) {
	auto variable = context.freshTypeVariable(that.position);

	auto calle = semanticExpression(that.calle, context);
	auto argument = semanticExpression(that.argument, context);
	context.typeCheck(calle.type, make!TypeFunction(variable, argument.type), that.position);
	return make!Call(variable, calle, argument);
}

CompileTimeExpression semanticImpl(Parser.Slice that, Context context) {
	auto array = semanticExpression(that.array, context);
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	auto type = make!TypeArray(context.freshTypeVariable(that.position));
	context.typeCheck(array.type, type, that.position);
	context.typeCheck(left.type, make!TypeInt(0, false), that.position);
	context.typeCheck(right.type, make!TypeInt(0, false), that.position);
	return make!Slice(array.type, array, left, right);
}

CompileTimeExpression semanticImpl(Parser.Binary!"->" that, Context context) {
	auto left = semanticMain(that.left, context).assumeType(that.left.position);
	auto right = semanticMain(that.right, context).assumeType(that.right.position);
	return make!TypeFunction(right, left);
}

//todo remove me
//wierd compiler bug

alias ParserBinary = Parser.Binary;
alias ParserPrefix = Parser.Prefix;

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (["<=", ">=", ">", "<"].canFind(op)) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	context.typeCheck(left.type, right.type, that.position);
	return make!(Binary!op)(make!TypeBool, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	auto type = context.freshTypeVariable(that.position, [make!PredicateNumber.convert!Predicate]);
	context.typeCheck(left.type, type, that.position);
	context.typeCheck(right.type, type, that.position);
	return make!(Binary!op)(left.type, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (["==", "!="].canFind(op)) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	context.typeCheck(left.type, right.type, that.position);
	return make!(Binary!op)(make!TypeBool(), left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (["&&", "||"].canFind(op)) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	context.typeCheck(left.type, make!TypeBool(), that.position);
	context.typeCheck(right.type, make!TypeBool(), that.position);
	return make!(Binary!op)(make!TypeBool, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (op == "~") {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	context.typeCheck(left.type, make!TypeArray(right.type), that.position);
	return make!(Binary!op)(left.type, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserPrefix!op that, Context context) if (op == "!") {
	auto value = semanticExpression(that.value, context);
	context.typeCheck(value.type, make!TypeBool(), that.position);
	return make!(Prefix!op)(make!TypeBool, value);
}

CompileTimeExpression semanticImpl(string op)(ParserPrefix!op that, Context context) if (op == "-") {
	auto value = semanticExpression(that.value, context);
	auto type = context.freshTypeVariable(that.position, [make!PredicateNumber.convert!Predicate]);
	context.typeCheck(value.type, type, that.position);
	return make!(Prefix!op)(value.type, value);
}

CompileTimeExpression semanticImpl(string op)(ParserPrefix!op that, Context context) if (op == "*") {
	auto value = semanticExpression(that.value, context);
	auto variable = context.freshTypeVariable(that.position);
	context.typeCheck(value.type, make!TypePointer(variable), that.position);
	return make!Deref(variable, value);
}

CompileTimeExpression semanticImpl(string op)(ParserPrefix!op that, Context context) if (["+", "/"].canFind(op)) {
	error(op ~ " not supported", that.position);
	return null;
}

Expression semanticImpl(Parser.Assign that, Context context) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	auto variable = context.freshTypeVariable(that.position);
	context.typeCheck(left.type, make!TypePointer(variable), that.position);
	context.typeCheck(variable, right.type, that.position);
	return make!Assign(make!TypeStruct(emptyArray!Type), left, right);
}

Expression semanticImpl(Parser.VariableDef that, Context context) {
	auto previous = context.locals;
	auto value = semanticExpression(that.value, context);
	auto variable = semanticPattern(that.variable, context);
	context.typeCheck(variable.type, value.type, that.position);
	auto lastSemantic = semanticExpression(that.last, context);
	context.locals = previous;
	return make!VariableDef(lastSemantic.type, variable, value, lastSemantic);
}

Pattern semanticPattern(Parser.Pattern pattern, Context context) {
	return dispatch!(semanticPatternImpl, Parser.NamedArgument, Parser.TupleArgument)(pattern, context);
}

Pattern semanticPatternImpl(Parser.NamedArgument that, Context context) {
	auto type = context.freshTypeVariable(that.position);
	auto variable = make!Variable(type, that.name, new VarId);
	context.bindVariable(variable, that.position);
	return make!NamedPattern(type, variable);
}

Pattern semanticPatternImpl(Parser.TupleArgument that, Context context) {
	auto matches = that.matches.map!(a => semanticPattern(a, context)).array;
	auto type = make!TypeStruct(matches.map!(a => a.type).array);
	return make!TuplePattern(type, matches);
}

CompileTimeExpression semanticImpl(Parser.FuncLit that, Context context) {
	error("only top level lambda are supported for now", that.position);
	return null;
}

CompileTimeExpression semanticImpl(Parser.StringLit that, Context context) {
	return make!StringLit(make!TypeArray(make!TypeChar()), that.value);
}

CompileTimeExpression semanticImpl(Parser.ArrayLit that, Context context) {
	auto variable = context.freshTypeVariable(that.position);
	auto type = make!TypeArray(variable);
	auto values = that.values.map!(a => semanticExpression(a, context)).array;
	foreach (value; values) {
		context.typeCheck(variable, value.type, that.position);
	}

	return make!ArrayLit(type, values);
}

CompileTimeExpression semanticImpl(Parser.ExternJs that, Context context) {
	auto variable = context.freshTypeVariable(that.position);
	return make!ExternJs(variable, that.name);
}
