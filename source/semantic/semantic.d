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
import misc;

struct Equivalence {
	Type left;
	Type right;
	Position position;
	int line;
	this(Type left, Type right, Position position, int line = __LINE__) {
		this.left = left;
		this.right = right;
		this.position = position;
		this.line = line;
		assert(left);
		assert(right);
	}

	string toString() {
		return left.to!string ~ " ~ " ~ right.to!string;
	}
}

class Context {
	Variable[] locals;
	void delegate(Type left, Type right, Position position, int line) typecheckField;
	CompileTimeExpression delegate(string name) searchGlobalVariable;

	this(Variable[] locals, void delegate(Type left, Type right, Position position, int line) typecheckField, CompileTimeExpression delegate(string name) searchGlobalVariable) {
		this.locals = locals;
		this.typecheckField = typecheckField;
		this.searchGlobalVariable = searchGlobalVariable;
	}

	void typecheck(Type left, Type right, Position position, int line = __LINE__) {
		typecheckField(left, right, position, line);
	}
}

CompileTimeExpression search(Context context, string name) {
	foreach (variable; context.locals.retro) {
		if (variable.name == name) {
			return variable;
		}
	}
	return context.searchGlobalVariable(name);
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

Type[PolymorphicVariable] unifyImpl(Equivalence[] equations) {
	if (equations.length == 0) {
		return null;
	}
	auto head = equations[0];
	Type[PolymorphicVariable] substitions = typeMatch(head.left, head.right, head.position);
	auto tail = equations[1 .. $];
	foreach (ref equation; tail) {
		equation.left = equation.left.specialize(substitions);
		equation.right = equation.right.specialize(substitions);
	}
	return mergeMaps(substitions, unifyImpl(tail));
}

Type[PolymorphicVariable] fixDefers(Type[PolymorphicVariable] substitions) {
	substitions = substitions.dup;
	foreach (ref type; substitions) {
		while (type.generics.byKey.map!(a => a in substitions).any) {
			type = type.specialize(substitions);
		}
	}
	foreach (type; substitions) {
		assert(!type.generics.byKey.map!(a => a in substitions).any);
	}
	return substitions;
}

// the heart of the compiler
Type[PolymorphicVariable] unify(Equivalence[] equations) {
	return fixDefers(unifyImpl(equations));
}

CompileTimeExpression searchGlobal(string name, Module mod, Tuple!()[Parser.ModuleVarDef] recursionCheck) {
	if (name in mod.aliases) {
		return mod.aliases[name].element;
	} else if (name in mod.rawSymbols) {
		return semanticGlobal(mod.rawSymbols[name], mod, recursionCheck);
	} else {
		return null;
	}
}

CompileTimeExpression semanticGlobal(Parser.ModuleVarDef symbol, Module mod, Tuple!()[Parser.ModuleVarDef] recursionCheck) {
	if (symbol in recursionCheck) {
		error("Illegal Recursion", symbol.position);
	}
	recursionCheck[symbol] = Tuple!()();

	Equivalence[] typechecks;

	void typecheck(Type left, Type right, Position position, int line = __LINE__) {
		typechecks ~= Equivalence(left, right, position, line);
	}

	CompileTimeExpression searchGlobalVariable(string name) {
		return searchGlobal(name, mod, recursionCheck);
	}

	Context context = new Context([], &typecheck, &searchGlobalVariable);

	Type type;
	if (symbol.explicitType) {
		type = symbol.explicitType.semanticType(context);
	}

	CompileTimeExpression applyTypeChecks(CompileTimeExpression expression0) {
		if (auto expression1 = expression0.castTo!Expression) {
			Type[PolymorphicVariable] substitions = unify(typechecks);
			//writeln("substition map for ", symbol.name, ": ", substitions);
			auto result = expression1.specialize(substitions);
			//writeln("type for ", symbol.name,": ", result.type);
			return result;
		} else {
			return expression0;
		}
	}

	// for recursive ast nodes that may reference them selfs
	void preassign(CompileTimeExpression expression) {
		mod.aliases[symbol.name] = ModuleAlias(expression, symbol.visible);
	}

	auto expression0 = semanticGlobalDispatch(symbol.value, symbol.name, type, context, &preassign);
	auto expression1 = applyTypeChecks(expression0);
	mod.aliases[symbol.name] = ModuleAlias(expression1, symbol.visible);
	if (auto expression2 = expression1.castTo!Symbol) {
		if (expression2.strong && expression2.generics.length == 0) {
			mod.exports[symbol.name] = expression2;
		}
	}
	return expression1;
}

CompileTimeExpression semanticGlobalDispatch(Parser.Expression that, string name, /* nullable */ Type type, Context context, void delegate(CompileTimeExpression) preassign) {
	return dispatch!(semanticGlobalImpl, Parser.Variable, Parser.TypeTuple, Parser.Index, Parser.TupleIndex, Parser.TupleIndexAddress, Parser.IndexAddress, Parser.Call, Parser.Length, Parser.TypeBool, Parser.TypeChar, Parser.TypeInt, Parser.Import, Parser.IntLit, Parser.CharLit, Parser.BoolLit, Parser.TupleLit, Parser.If, Parser.While, Parser.New, Parser.NewArray, Parser.Cast, Parser.Infer, Parser.Slice, Parser.Scope, Parser.FuncLit, Parser.StringLit, Parser.ArrayLit, Parser.ExternJs, Parser.Binary!"*", Parser.Binary!"/", Parser.Binary!"%", Parser.Binary!"+", Parser.Binary!"-", Parser.Binary!"~", Parser.Binary!"==", Parser.Binary!"!=", Parser.Binary!"<=", Parser.Binary!">=", Parser.Binary!"<", Parser.Binary!">", Parser.Binary!"&&", Parser.Binary!"||", Parser.Prefix!"-", Parser.Prefix!"*", Parser.Prefix!"!", Parser.Postfix!"(*)", Parser.Postfix!"[*]", Parser.Binary!"->", Parser.UseSymbol)(that, name, type, context, preassign);
}

CompileTimeExpression semanticGlobalImpl(Parser.FuncLit that, string name, Type annotation, Context context, void delegate(CompileTimeExpression) preassign) {
	auto argument = semanticPattern(that.argument, context);
	auto returnType = make!Scheme(make!PolymorphicVariable());
	auto type = make!TypeFunction(returnType, argument.type);
	auto generics = type.generics;
	if (annotation) {
		context.typecheck(type, annotation, that.position);
	}
	// has side effects
	Expression get() {
		return semanticPolymorphic(that.text, context);
	}

	auto result = make!FunctionLiteral(type, generics, name, !!annotation, new SymbolId, argument, defer(&get));
	preassign(result);
	result.text.eval; // required to collect unification constraints
	return result;
}

CompileTimeExpression semanticGlobalImpl(T)(T that, string name, Type annotation, Context context, void delegate(CompileTimeExpression) preassign) {
	auto expression = semanticMain(that, context);
	if (annotation) {
		// todo fix this
		auto runtime = expression.assumePolymorphic(that.position);
		context.typecheck(runtime.type, annotation, that.position);
	}
	return expression;
}

Type assumeType(CompileTimeExpression value, Position position, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!Type, "Expected type", position, file, line);
	return value.castTo!Type;
}

Expression assumePolymorphic(CompileTimeExpression value, Position position, string file = __FILE__, int line = __LINE__) {
	auto result = value.castTo!Expression;
	check(result, "Expected polymorphic value", position, file, line);

	return result;
}

Type semanticType(Parser.Expression that, Context context) {
	return assumeType(semanticMain(that, context), that.position);
}

Expression semanticPolymorphic(Parser.Expression that, Context context) {
	return assumePolymorphic(semanticMain(that, context), that.position);
}

auto semanticMain(Parser.Expression that, Context context) {
	auto result = semanticImplDispatch(that, context);
	return result;
}

CompileTimeExpression semanticImplDispatch(Parser.Expression that, Context context) {
	return dispatch!(semanticImpl, Parser.Variable, Parser.TypeTuple, Parser.Index, Parser.IndexAddress, Parser.TupleIndex, Parser.TupleIndexAddress, Parser.Call, Parser.Length, Parser.TypeBool, Parser.TypeChar, Parser.TypeInt, Parser.Import, Parser.IntLit, Parser.CharLit, Parser.BoolLit, Parser.TupleLit, Parser.If, Parser.While, Parser.New, Parser.NewArray, Parser.Cast, Parser.Infer, Parser.Slice, Parser.Scope, Parser.FuncLit, Parser.StringLit, Parser.ArrayLit, Parser.ExternJs, Parser.Binary!"*", Parser.Binary!"/", Parser.Binary!"%", Parser.Binary!"+", Parser.Binary!"-", Parser.Binary!"~", Parser.Binary!"==", Parser.Binary!"!=", Parser.Binary!"<=", Parser.Binary!">=", Parser.Binary!"<", Parser.Binary!">", Parser.Binary!"&&", Parser.Binary!"||", Parser.Prefix!"-", Parser.Prefix!"*", Parser.Prefix!"!", Parser.Postfix!"(*)", Parser.Postfix!"[*]", Parser.Binary!"->", Parser.UseSymbol)(that, context);
}

CompileTimeExpression semanticImpl(Parser.Variable that, Context context) {
	auto variable = context.search(that.name);
	check(!(variable is null), "Undefined variable", that.position);
	//todo check for closrure variable
	return variable;
}

CompileTimeExpression semanticImpl(Parser.TypeTuple that, Context context) {
	auto types = that.values.map!(a => semanticType(a, context)).array;
	return make!TypeStruct(types);
}

CompileTimeExpression semanticImpl(Parser.UseSymbol that, Context context) {
	auto value = semanticMain(that.value, context);
	check(value.castTo!Import, "scope resolution expect a module", that.position);
	auto mod = value.castTo!Import.mod;
	check(that.index in mod.aliases, "unknown module symbol", that.position);
	check(mod.aliases[that.index].visible, that.index ~ "is not visible", that.position);
	return mod.aliases[that.index].element;
}

CompileTimeExpression semanticImpl(Parser.Length that, Context context) {
	auto variable = make!Scheme(make!PolymorphicVariable);
	auto type = make!TypeFunction(make!TypeInt(0, false), make!TypeArray(variable));
	return make!Length(type, type.generics);
}

CompileTimeExpression semanticImpl(Parser.Import that, Context context) {
	return make!Import(that.mod);
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
	auto variable = make!Scheme(make!PolymorphicVariable(), [make!ConstraintNumber.convert!Constraint]);
	return make!IntLit(variable, variable.generics, that.value);
}

CompileTimeExpression semanticImpl(Parser.CharLit that, Context context) {
	return make!CharLit(make!TypeChar(), null, that.value);
}

CompileTimeExpression semanticImpl(Parser.BoolLit that, Context context) {
	return make!BoolLit(make!TypeBool(), null, that.yes);
}

CompileTimeExpression semanticImpl(Parser.TupleLit that, Context context) {
	auto values = that.values.map!(a => semanticPolymorphic(a, context)).array;
	return make!TupleLit(make!TypeStruct(values.map!(a => a.type).array), values.map!(a => a.generics)
			.fold!mergeSets(emptySet!PolymorphicVariable), values);
}

CompileTimeExpression semanticImpl(Parser.If that, Context context) {
	auto cond = semanticPolymorphic(that.cond, context);
	auto yes = semanticPolymorphic(that.yes, context);
	auto no = semanticPolymorphic(that.no, context);
	context.typecheck(cond.type, make!TypeBool(), that.cond.position);
	context.typecheck(yes.type, no.type, that.position);
	auto generics = mergeSets(cond.generics, yes.generics, no.generics);
	return make!If(yes.type, generics, cond, yes, no);
}

CompileTimeExpression semanticImpl(Parser.While that, Context context) {
	auto cond = semanticPolymorphic(that.cond, context);
	auto state = semanticPolymorphic(that.state, context);
	context.typecheck(cond.type, make!TypeBool(), that.cond.position);
	auto generics = mergeSets(cond.generics, state.generics);
	return make!While(make!TypeStruct(emptyArray!Type), generics, cond, state);
}

CompileTimeExpression semanticImpl(Parser.New that, Context context) {
	auto value = semanticPolymorphic(that.value, context);
	return make!New(make!TypePointer(value.type), value.generics, value);
}

CompileTimeExpression semanticImpl(Parser.NewArray that, Context context) {
	auto length = semanticPolymorphic(that.length, context);
	auto value = semanticPolymorphic(that.value, context);
	auto generics = mergeSets(length.generics, value.generics);
	context.typecheck(length.type, make!TypeInt(0, false), that.length.position);
	return make!NewArray(make!TypeArray(value.type), generics, length, value);
}

CompileTimeExpression semanticImpl(Parser.Cast that, Context context) {
	auto wanted = semanticType(that.type, context);
	auto value = semanticPolymorphic(that.value, context);
	auto expected = make!Scheme(make!PolymorphicVariable, [make!ConstraintNumber.convert!Constraint]);
	context.typecheck(value.type, expected, that.value.position);

	auto valid = make!Scheme(make!PolymorphicVariable, [make!ConstraintNumber.convert!Constraint]);
	context.typecheck(wanted, valid, that.position);

	return make!CastInteger(wanted, value.generics, value);
}

CompileTimeExpression semanticImpl(Parser.Infer that, Context context) {
	auto argumentType = semanticType(that.type, context);
	auto value = semanticPolymorphic(that.value, context);
	context.typecheck(argumentType, value.type, that.position);
	return value;
}

CompileTimeExpression semanticImpl(Parser.Index that, Context context) {
	auto array = semanticPolymorphic(that.array, context);
	auto index = semanticPolymorphic(that.index, context);
	auto variable = make!Scheme(make!PolymorphicVariable());
	auto generics = mergeSets(variable.generics, array.generics, index.generics);
	context.typecheck(array.type, make!TypeArray(variable), that.array.position);
	context.typecheck(index.type, make!TypeInt(0, false), that.index.position);
	return make!Index(variable, generics, array, index);
}

CompileTimeExpression semanticImpl(Parser.IndexAddress that, Context context) {
	auto array = semanticPolymorphic(that.array, context);
	auto index = semanticPolymorphic(that.index, context);
	auto variable = make!Scheme(make!PolymorphicVariable());
	auto generics = mergeSets(variable.generics, array.generics, index.generics);
	context.typecheck(array.type, make!TypeArray(variable), that.array.position);
	context.typecheck(index.type, make!TypeInt(0, false), that.index.position);
	return make!IndexAddress(make!TypePointer(variable), generics, array, index);
}

CompileTimeExpression semanticImpl(Parser.TupleIndex that, Context context) {
	auto tuple = semanticPolymorphic(that.tuple, context);
	auto index = that.index;

	auto type = make!Scheme(make!PolymorphicVariable);
	auto tupletype = make!Scheme(make!PolymorphicVariable, [make!ConstraintTuple(that.index, type).convert!Constraint]);
	auto generics = mergeSets(tupletype.generics, type.generics);
	context.typecheck(tuple.type, tupletype, that.position);
	return make!TupleIndex(type, generics, tuple, index);
}

CompileTimeExpression semanticImpl(Parser.TupleIndexAddress that, Context context) {
	auto tuple = semanticPolymorphic(that.tuple, context);
	auto index = that.index;
	auto variable = make!Scheme(make!PolymorphicVariable);
	auto tupletype = make!TypePointer(make!Scheme(make!PolymorphicVariable, [make!ConstraintTuple(that.index, variable).convert!Constraint]));
	auto generics = mergeSets(variable.generics, tuple.generics);
	context.typecheck(tuple.type, tupletype, that.position);
	return make!TupleIndexAddress(make!TypePointer(variable), generics, tuple, index);
}

CompileTimeExpression semanticImpl(Parser.Call that, Context context) {
	auto variable = make!Scheme(make!PolymorphicVariable());

	auto calle = semanticPolymorphic(that.calle, context);
	auto argument = semanticPolymorphic(that.argument, context);

	auto generics = mergeSets(variable.generics, calle.generics, argument.generics);
	context.typecheck(calle.type, make!TypeFunction(variable, argument.type), that.position);
	return make!Call(variable, generics, calle, argument);
}

CompileTimeExpression semanticImpl(Parser.Slice that, Context context) {
	auto array = semanticPolymorphic(that.array, context);
	auto left = semanticPolymorphic(that.left, context);
	auto right = semanticPolymorphic(that.right, context);
	auto type = make!TypeArray(make!Scheme(make!PolymorphicVariable()));
	auto generics = mergeSets(type.generics, array.generics, left.generics, right.generics);
	context.typecheck(array.type, type, that.position);
	context.typecheck(left.type, make!TypeInt(0, false), that.position);
	context.typecheck(right.type, make!TypeInt(0, false), that.position);
	return make!Slice(array.type, generics, array, left, right);
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
	auto left = semanticPolymorphic(that.left, context);
	auto right = semanticPolymorphic(that.right, context);
	auto generics = mergeSets(left.generics, right.generics);
	context.typecheck(left.type, right.type, that.position);
	return make!(Binary!op)(make!TypeBool, generics, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = semanticPolymorphic(that.left, context);
	auto right = semanticPolymorphic(that.right, context);
	auto type = make!Scheme(make!PolymorphicVariable, [make!ConstraintNumber.convert!Constraint]);
	auto generics = mergeSets(type.generics, left.generics, right.generics);
	context.typecheck(left.type, type, that.position);
	context.typecheck(right.type, type, that.position);
	return make!(Binary!op)(left.type, generics, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (["==", "!="].canFind(op)) {
	auto left = semanticPolymorphic(that.left, context);
	auto right = semanticPolymorphic(that.right, context);
	auto generics = mergeSets(left.generics, right.generics);
	context.typecheck(left.type, right.type, that.position);
	return make!(Binary!op)(make!TypeBool(), generics, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (["&&", "||"].canFind(op)) {
	auto left = semanticPolymorphic(that.left, context);
	auto right = semanticPolymorphic(that.right, context);
	auto generics = mergeSets(left.generics, right.generics);
	context.typecheck(left.type, make!TypeBool(), that.position);
	context.typecheck(right.type, make!TypeBool(), that.position);
	return make!(Binary!op)(make!TypeBool, generics, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserBinary!op that, Context context) if (op == "~") {
	auto left = semanticPolymorphic(that.left, context);
	auto right = semanticPolymorphic(that.right, context);
	auto generics = mergeSets(left.generics, right.generics);
	context.typecheck(left.type, make!TypeArray(right.type), that.position);
	return make!(Binary!op)(left.type, generics, left, right);
}

CompileTimeExpression semanticImpl(string op)(ParserPrefix!op that, Context context) if (op == "!") {
	auto value = semanticPolymorphic(that.value, context);
	context.typecheck(value.type, make!TypeBool(), that.position);
	return make!(Prefix!op)(make!TypeBool, value.generics, value);
}

CompileTimeExpression semanticImpl(string op)(ParserPrefix!op that, Context context) if (op == "-") {
	auto value = semanticPolymorphic(that.value, context);
	auto type = make!Scheme(make!PolymorphicVariable, [make!ConstraintNumber.convert!Constraint]);
	auto generics = mergeSets(type.generics, value.generics);
	context.typecheck(value.type, type, that.position);
	return make!(Prefix!op)(value.type, generics, value);
}

CompileTimeExpression semanticImpl(string op)(ParserPrefix!op that, Context context) if (op == "*") {
	auto value = semanticPolymorphic(that.value, context);
	auto variable = make!Scheme(make!PolymorphicVariable());
	auto generics = mergeSets(variable.generics, value.generics);
	context.typecheck(value.type, make!TypePointer(variable), that.position);
	return make!Deref(variable, generics, value);
}

CompileTimeExpression semanticImpl(string op)(ParserPrefix!op that, Context context) if (["+", "/"].canFind(op)) {
	error(op ~ " not supported", that.position);
	return null;
}

Expression semanticScope(Parser.Statement[] tail, Parser.Expression last, Context context) {
	if (tail.length == 0) {
		auto otherwise = make!TupleLit(make!TypeStruct(emptyArray!Type), emptySet!PolymorphicVariable, emptyArray!Expression);
		return last ? semanticPolymorphic(last, context) : otherwise;
	} else {
		auto head = tail[0];
		auto node = dispatch!(semanticScopeImpl, Parser.Assign, Parser.VariableDef, Parser.Expression)(head, tail[1 .. $], last, context);
		return node;
	}
}

Expression semanticScopeImpl(Parser.Assign that, Parser.Statement[] tail, Parser.Expression last, Context context) {
	auto left = semanticPolymorphic(that.left, context);
	auto right = semanticPolymorphic(that.right, context);
	auto variable = make!Scheme(make!PolymorphicVariable());
	context.typecheck(left.type, make!TypePointer(variable), that.position);
	context.typecheck(variable, right.type, that.position);
	auto end = semanticScope(tail, last, context);
	auto generics = mergeSets(left.generics, right.generics, end.generics);
	return make!Assign(end.type, generics, left, right, end);
}

Expression semanticScopeImpl(Parser.VariableDef that, Parser.Statement[] tail, Parser.Expression last, Context context) {
	auto value = semanticPolymorphic(that.value, context);
	auto variable = semanticPattern(that.variable, context);
	context.typecheck(variable.type, value.type, that.position);
	auto lastSemantic = semanticScope(tail, last, context);
	return make!VariableDef(lastSemantic.type, mergeSets(variable.generics, lastSemantic.generics), variable, value, lastSemantic);
}

Expression semanticScopeImpl(Parser.Expression that, Parser.Statement[] tail, Parser.Expression last, Context context) {
	auto stateful = semanticPolymorphic(that, context);
	context.typecheck(stateful.type, make!TypeStruct(emptyArray!Type), that.position);
	auto end = semanticScope(tail, last, context);
	auto generics = mergeSets(stateful.generics, end.generics);
	return make!Scope(end.type, generics, stateful, end);
}

CompileTimeExpression semanticImpl(Parser.Scope that, Context context) {
	return semanticScope(that.states, that.last, context);
}

Pattern semanticPattern(Parser.Pattern pattern, Context context) {
	return dispatch!(semanticPatternImpl, Parser.NamedArgument, Parser.TupleArgument)(pattern, context);
}

Pattern semanticPatternImpl(Parser.NamedArgument pattern, Context context) {
	auto type = make!Scheme(make!PolymorphicVariable());
	auto variable = make!Variable(type, type.generics, pattern.name, new VarId);
	context.locals ~= variable;
	return make!NamedPattern(type, type.generics, variable);
}

Pattern semanticPatternImpl(Parser.TupleArgument pattern, Context context) {
	auto matches = pattern.matches.map!(a => semanticPattern(a, context)).array;
	auto type = make!TypeStruct(matches.map!(a => a.type).array);
	auto generics = matches.map!(a => a.generics)
		.fold!mergeSets(emptySet!PolymorphicVariable);
	return make!TuplePattern(type, generics, matches);
}

CompileTimeExpression semanticImpl(Parser.FuncLit that, Context context) {
	error("only top level lambda are supported for now", that.position);
	return null;
}

CompileTimeExpression semanticImpl(Parser.StringLit that, Context context) {
	return make!StringLit(make!TypeArray(make!TypeChar()), null, that.value);
}

CompileTimeExpression semanticImpl(Parser.ArrayLit that, Context context) {
	auto variable = make!Scheme(make!PolymorphicVariable);
	auto type = make!TypeArray(variable);
	auto values = that.values.map!(a => semanticPolymorphic(a, context)).array;
	auto generics = values.map!(a => a.generics)
		.fold!mergeSets(emptySet!PolymorphicVariable).mergeSets(type.generics);
	foreach (value; values) {
		context.typecheck(variable, value.type, that.position);
	}

	return make!ArrayLit(type, generics, values);
}

CompileTimeExpression semanticImpl(Parser.ExternJs that, Context context) {
	auto variable = make!Scheme(make!PolymorphicVariable);
	return make!ExternJs(variable, variable.generics, that.name);
}
