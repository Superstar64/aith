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

import app : knownSymbols, readSemanticModule;
import Parser = parser.ast;
import semantic.astimpl;

import misc.nonstrict;
import misc.position;
import misc.container;
import misc.misc;

struct TypeCheckerFrame {
	TypeCheckerFrame* next;
	TypeChecker* typeChecker;
	bool referenced;

	void unifyTypeCheckers() {
		if (next) {
			next.referenced = true;
			moveTypeChecker(*next.typeChecker, *typeChecker);
			*next.typeChecker = *typeChecker;
			next.unifyTypeCheckers();
		}
	}
}

class TypeChecker {
	Dictonary!(Parser.ModuleVarDef, Term) bindingGroup;
	Dictonary!(TypeVariableId, Position) freshVariables;
	Equivalence[] typeChecks;
}

void evaluateTypeChecks(TypeChecker typeChecker) {
	auto substitution = typeMatch(typeChecker.typeChecks);
	foreach (symbol, expression0; typeChecker.bindingGroup.range) {
		auto allowed = expression0.type.specialize(substitution).freeVariables.keys;
		foreach (variable, position; typeChecker.freshVariables.range) {
			auto valid = variable in substitution && isSubSet(substitution[variable].freeVariables.keys, allowed);
			if (!valid) {
				error("Unable to infer type variable", position);
			}
		}

		auto expression1 = expression0.specialize(substitution);
		//remove rigidity
		auto fresh = expression1.type.freshFlexibleSubstitution;
		auto expression2 = expression1.specialize(fresh);

		knownSymbols[symbol] = expression2;
	}
}

void moveTypeChecker(TypeChecker from, TypeChecker to) {
	if (from is to) {
		return;
	}
	foreach (def, term; from.bindingGroup.range) {
		to.bindingGroup[def] = term;
	}
	foreach (id, position; from.freshVariables.range) {
		to.freshVariables[id] = position;
	}
	foreach (check; from.typeChecks) {
		to.typeChecks ~= check;
	}
}

struct SelfReferential {
	//nullable
	Expression expression;
	TypeCheckerFrame* children;
}

struct RecursionChecker {
	TypeCheckerFrame* frame;
	Dictonary!(Parser.ModuleVarDef, SelfReferential) recursive;
}

enum Linearity {
	unused,
	linear,
	unrestricted
}

Linearity use(Linearity uses) {
	if (uses == Linearity.unused) {
		return Linearity.linear;
	} else {
		return Linearity.unrestricted;
	}
}

Linearity both(Linearity left, Linearity right) {
	if (left == Linearity.unused) {
		return right;
	} else if (right == Linearity.unused) {
		return left;
	} else {
		return Linearity.unrestricted;
	}
}

Linearity branch(Linearity left, Linearity right) {
	if (left == Linearity.unused && right == Linearity.unused) {
		return Linearity.unused;
	} else if (left == Linearity.linear && right == Linearity.linear) {
		return Linearity.linear;
	} else {
		return Linearity.unrestricted;
	}
}

class Context {
	// initialized when processing symbol
	Dictonary!(string, Parser.ModuleVarDef) rawGlobalSymbols;
	RigidContext rigidContext;
	RecursionChecker recursionCheck;

	// mutable data
	TypeChecker typeChecker;
	Dictonary!(string, Binding[]) locals;
	Dictonary!(VarId, Linearity) uses;

	this(Dictonary!(string, Parser.ModuleVarDef) rawGlobalSymbols, string symbolName, RecursionChecker recursionCheck) {
		this.rawGlobalSymbols = rawGlobalSymbols;
		this.rigidContext = make!RigidContext(symbolName);
		this.typeChecker = new TypeChecker;
		recursionCheck.frame.typeChecker = &typeChecker;
		this.recursionCheck = recursionCheck;
	}

	void typeCheck(Type left, Type right, Position position) {
		typeChecker.typeChecks ~= Equivalence(left, right, position);
	}

	void bindTypeVariable(TypeVariable variable, Position position, bool duplicate) {
		locals = locals.insertIfMissing(variable.name, emptyArray!Binding);

		if (!duplicate && locals[variable.name].length != 0) {
			error("duplicate name", position);
		}
		locals[variable.name] = locals[variable.name] ~ variable;
	}

	void bindTermVariable(Variable variable, Position position, bool duplicate) {
		locals = locals.insertIfMissing(variable.name, emptyArray!Binding);

		if (!duplicate && locals[variable.name].length != 0) {
			error("duplicate name", position);
		}
		locals[variable.name] = locals[variable.name] ~ variable;
		uses[variable.id] = Linearity.unused;
	}

	void removeTermVariable(Variable variable, Position position) {
		import misc.container : remove;

		if (uses[variable.id] != Linearity.linear) {
			auto fresh = this.freshTypeVariable(position, make!PredicateUnrestricted.constraintsFrom);
			this.typeCheck(variable.type, fresh, position);
		}
		locals[variable.name] = locals[variable.name][0 .. $ - 1];
		uses.remove(variable.id);
	}
}

Expression search(Context context, string name, Position position) {
	if (name in context.locals && context.locals[name].length > 0) {
		if (auto variable = context.locals[name][$ - 1].castTo!Variable) {
			assert(variable.id in context.uses);
			context.uses[variable.id] = context.uses[variable.id].use;
		}
		return context.locals[name][$ - 1];
	}
	return searchGlobal(context, name, position);
}

Expression builtinImpl(string name : "new")() {
	auto variable = freshGlobalTypeVariable;
	auto argument = typeStructFrom(variable, make!TypeWorld);
	auto result = typeStructFrom(make!TypeOwnPointer(variable), make!TypeWorld);
	auto type = make!TypeFunction(result, argument);
	return make!(Desugar!"new")(type);
}

Expression builtinImpl(string name : "delete")() {
	auto variable = freshGlobalTypeVariable;
	auto argument = typeStructFrom(make!TypeOwnPointer(variable), make!TypeWorld);
	auto result = typeStructFrom(variable, make!TypeWorld);
	auto type = make!TypeFunction(result, argument);
	return make!(Desugar!"delete")(type);
}

Expression builtinImpl(string name : "borrow")() {
	auto variable = freshGlobalTypeVariable;
	auto type = make!TypeFunction(typeStructFrom(make!TypePointer(variable), make!TypeOwnPointer(variable)), make!TypeOwnPointer(variable));
	return make!(Desugar!"borrow")(type);
}

Expression builtinImpl(string name : "true")() {
	return make!BoolLit(make!TypeBool(), true);
}

Expression builtinImpl(string name : "false")() {
	return make!BoolLit(make!TypeBool(), false);
}

Expression builtinImpl(string name : "cast")() {
	auto wanted = freshGlobalTypeVariable(make!PredicateNumber.constraintsFrom);
	auto input = freshGlobalTypeVariable(make!PredicateNumber.constraintsFrom);
	auto type = make!TypeFunction(wanted, input);
	return make!CastInteger(type, wanted, input);
}

Expression builtinImpl(string name : "length")() {
	auto variable = freshGlobalTypeVariable;
	auto type = make!TypeFunction(make!TypeInt(0, false), make!TypeArray(variable));
	return make!(Desugar!"length")(type);
}

Expression builtinImpl(string name : "new array")() {
	auto variable = freshGlobalTypeVariable(make!PredicateUnrestricted.constraintsFrom);
	auto arguments = typeStructFrom(make!TypeInt(0, false), variable);
	auto type = make!TypeFunction(make!TypeOwnArray(variable), arguments);
	return make!(Desugar!"new array")(type);
}

Expression builtinImpl(string name : "delete array")() {
	auto variable = freshGlobalTypeVariable;
	auto type = make!TypeFunction(typeStructFrom, make!TypeOwnArray(variable));
	return make!(Desugar!"delete array")(type);
}

Expression builtinImpl(string name : "borrow array")() {
	auto variable = freshGlobalTypeVariable;
	auto result = typeStructFrom(make!TypeArray(variable), make!TypeOwnArray(variable));
	auto type = make!TypeFunction(result, make!TypeOwnArray(variable));
	return make!(Desugar!"borrow array")(type);
}

Expression builtinImpl(string name : "boolean")() {
	return make!TypeBool();
}

Expression builtinImpl(string name : "character")() {
	return make!TypeChar();
}

Expression builtinImpl(string name : "equal")() {
	return make!PredicateEqual;
}

Expression builtinImpl(string name : "number")() {
	return make!PredicateNumber;
}

Expression builtinImpl(string name : "unrestricted")() {
	return make!PredicateUnrestricted;
}

Expression builtinImpl(string name : "world")() {
	return make!TypeWorld;
}

Expression builtinImpl(string name : "index address")() {
	auto variable = freshGlobalTypeVariable();
	auto argument = typeStructFrom(make!TypeArray(variable), make!TypeInt(0, false), make!TypeWorld);
	auto result = typeStructFrom(make!TypePointer(variable), make!TypeWorld);
	auto type = make!TypeFunction(result, argument);
	return make!(Desugar!"index address")(type);
}

Expression builtinImpl(string name : "assign")() {
	auto variable = freshGlobalTypeVariable(make!PredicateUnrestricted.constraintsFrom);
	auto argument = typeStructFrom(make!TypePointer(variable), variable, make!TypeWorld);
	auto result = make!TypeWorld;
	auto type = make!TypeFunction(result, argument);
	return make!(Desugar!"assign")(type);
}

Expression builtinImpl(string name : "integer")() {
	return make!TypeInt(0, true);
}

Expression builtinImpl(string name : "integer8")() {
	return make!TypeInt(8, true);
}

Expression builtinImpl(string name : "integer16")() {
	return make!TypeInt(16, true);
}

Expression builtinImpl(string name : "integer32")() {
	return make!TypeInt(32, true);
}

Expression builtinImpl(string name : "integer64")() {
	return make!TypeInt(64, true);
}

Expression builtinImpl(string name : "natural")() {
	return make!TypeInt(0, false);
}

Expression builtinImpl(string name : "natural8")() {
	return make!TypeInt(8, false);
}

Expression builtinImpl(string name : "natural16")() {
	return make!TypeInt(16, false);
}

Expression builtinImpl(string name : "natural32")() {
	return make!TypeInt(32, false);
}

Expression builtinImpl(string name : "natural64")() {
	return make!TypeInt(64, false);
}

ModuleDefinition builtin(string name)() {
	return ModuleDefinition(builtinImpl!name, true);
}

enum builtins = AliasSeq!("new", "true", "false", "cast", "length", "new array", "boolean", "character", "equal", "number", "unrestricted", "delete", "borrow", "delete array", "borrow array", "world", "index address", "assign", "integer", "integer8", "integer16", "integer32", "integer64", "natural", "natural8", "natural16", "natural32", "natural64");

Expression searchGlobal(Context context, string name, Position position) {
	static foreach (built; builtins) {
		if (name == built) {
			return context.unpackModuleDefinition(builtin!built, position);
		}
	}
	if (name in context.rawGlobalSymbols) {
		auto symbol = context.rawGlobalSymbols[name];
		auto resolved = resolveSymbol(context.rawGlobalSymbols, symbol, context.recursionCheck);
		return context.unpackModuleDefinition(resolved, position);
	} else {
		return null;
	}
}

Expression unpackModuleDefinition(Context context, ModuleDefinition resolved, Position position) {
	if (resolved.freshen) {
		if (auto term = resolved.get.castTo!Term) {
			auto fresh = term.type.freshSubstitution;
			fresh.freeVariables.byKey.each!(variable => context.typeChecker.freshVariables[variable] = position);
			return term.specialize(fresh);
		} else {
			return resolved.get;
		}
	} else {
		return resolved.get;
	}
}

ModuleDefinition resolveSymbol(Dictonary!(string, Parser.ModuleVarDef) rawSymbols, Parser.ModuleVarDef symbol, RecursionChecker recursionCheck) {
	if (symbol in knownSymbols) {
		return ModuleDefinition(knownSymbols[symbol], true);
	} else if (recursionCheck.frame && symbol in recursionCheck.frame.typeChecker.bindingGroup) {
		return ModuleDefinition(recursionCheck.frame.typeChecker.bindingGroup[symbol], false);
	} else if (symbol in recursionCheck.recursive) {
		auto assign = recursionCheck.recursive[symbol];
		if (assign.expression is null) {
			error("Illegal self reference", symbol.position);
		}
		assign.children.unifyTypeCheckers;
		return ModuleDefinition(assign.expression, false);
	} else {
		return ModuleDefinition(semanticGlobal(rawSymbols, symbol, recursionCheck), true);
	}
}

Module createModule(Parser.Module parser) {
	Dictonary!(string, Parser.ModuleVarDef) rawSymbols;
	foreach (symbol; parser.symbols) {
		check(!(symbol.name in rawSymbols), "Symbol already exists", symbol.position);
		rawSymbols[symbol.name] = symbol;
	}
	ModuleDefinition delegate(RecursionChecker) resolveSymbolThunk(Parser.ModuleVarDef symbol) {
		ModuleDefinition thunk(RecursionChecker recursionCheck) {
			return resolveSymbol(rawSymbols, symbol, recursionCheck);
		}

		return &thunk;
	}

	Dictonary!(string, ModuleDefinition delegate(RecursionChecker)) aliases;
	ModuleDefinition delegate(RecursionChecker)[] orderedAliases;
	foreach (symbol; parser.symbols) {
		auto value = resolveSymbolThunk(symbol);
		orderedAliases ~= value;
		aliases[symbol.name] = value;
	}
	auto ret = new Module;
	ret.aliases = aliases;
	ret.orderedAliases = orderedAliases;
	return ret;
}

void validateModule(Module mod) {
	foreach (symbol; mod.orderedAliases) {
		symbol(RecursionChecker());
	}
}

Dictonary!(PredicateId, Predicate) constraintsFrom(Predicate predicate) {
	return [predicate.id: predicate].fromAALiteral;
}

Dictonary!(PredicateId, Predicate) constraintsFrom(T...)(Predicate predicate, T tail) {
	return constraintsFrom(tail).insert(predicate.id, predicate);
}

TypeVariable freshGlobalTypeVariable(Dictonary!(PredicateId, Predicate) constraints = emptyMap!(PredicateId, Predicate), string name = null) {
	auto id = make!TypeVariableId(name);
	return make!TypeVariable(id, constraints, emptyMap!(RigidContext, RigidVariable));
}

TypeVariable freshTypeVariable(Context context, Position position, Dictonary!(PredicateId, Predicate) constraints = emptyMap!(PredicateId, Predicate), Dictonary!(RigidContext, RigidVariable) rigidity = emptyMap!(RigidContext, RigidVariable), string name = null) {
	auto id = make!TypeVariableId(name);
	context.typeChecker.freshVariables[id] = position;
	return make!TypeVariable(id, constraints, rigidity);
}

Expression semanticGlobal(Dictonary!(string, Parser.ModuleVarDef) parserGlobals, Parser.ModuleVarDef symbol, RecursionChecker recursionCheck) {
	assert(!(symbol in recursionCheck.recursive));

	auto frame = TypeCheckerFrame(null, null, false);
	if (recursionCheck.frame) {
		assert(!recursionCheck.frame.next);
		recursionCheck.frame.next = &frame;
	}
	scope (exit) {
		if (recursionCheck.frame) {
			assert(recursionCheck.frame.next);
			recursionCheck.frame.next = null;
		}
	}

	Context context = new Context(parserGlobals, symbol.name, RecursionChecker(&frame, recursionCheck.recursive));

	Type type;
	if (symbol.explicitType) {
		type = symbol.explicitType.semanticType(context);
	}

	auto expression = symbol.value.semanticGlobal(symbol.strong, symbol.name, type, context, symbol);

	if (auto expression1 = expression.castTo!Term) {
		context.typeChecker.bindingGroup[symbol] = expression1;
		if (frame.referenced) {
			return expression;
		} else {
			evaluateTypeChecks(context.typeChecker);
			return knownSymbols[symbol];
		}
	} else {
		assert(!frame.referenced);
		knownSymbols[symbol] = expression;
		return expression;
	}
}

Expression semanticGlobalImpl(Parser.FuncLit that, bool strong, string name, Type annotation, Context context, Parser.ModuleVarDef symbol) {
	auto argument = semanticPattern(that.argument, context);
	auto returnType = context.freshTypeVariable(that.position);
	auto type = make!TypeFunction(returnType, argument.type);
	if (annotation) {
		context.typeCheck(type, annotation, that.position);
	}
	// has side effects
	Term get() {
		return semanticExpression(that.text, context);
	}

	auto result = make!FunctionLiteral(type, name, strong ? Linkage.strong : Linkage.weak, new SymbolId, argument, defer(&get));
	context.recursionCheck.recursive[symbol] = SelfReferential(result, context.recursionCheck.frame);
	result.text.eval; // required to collect unification constraints
	context.typeCheck(result.text.get.type, returnType, that.position);
	argument.removeBindings(context, that.position);
	return result;
}

Expression semanticGlobalImpl(T)(T that, bool strong, string name, Type annotation, Context context, Parser.ModuleVarDef symbol) {
	context.recursionCheck.recursive[symbol] = SelfReferential(null, context.recursionCheck.frame);
	if (strong) {
		error("Expected symbol", that.position);
	}
	auto expression = semanticMain(that, context);
	if (annotation) {
		// todo fix this
		auto runtime = expression.assumeTerm(that.position);
		context.typeCheck(runtime.type, annotation, that.position);
	}
	return expression;
}

Type assumeType(Expression value, Position position, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!Type, "Expected type", position, file, line);
	return value.castTo!Type;
}

Predicate assumeConstraint(Expression value, Position position, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!Predicate, "Expected constraint", position, file, line);
	return value.castTo!Predicate;
}

Term assumeTerm(Expression value, Position position, string file = __FILE__, int line = __LINE__) {
	auto result = value.castTo!Term;
	check(result, "Expected a term", position, file, line);

	return result;
}

Pattern assumePattern(Expression value, Position position, string file = __FILE__, int line = __LINE__) {
	auto result = value.castTo!Pattern;
	check(result, "Expected pattern", position, file, line);

	return result;
}

Type semanticType(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeType(semanticMain(that, context), that.position, file, line);
}

Predicate semanticConstraint(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeConstraint(semanticMain(that, context), that.position, file, line);
}

Term semanticExpression(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeTerm(semanticMain(that, context), that.position, file, line);
}

Pattern semanticPattern(Parser.Pattern that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumePattern(semanticMain(that, context), that.position, file, line);
}

auto semanticMain(Parser.Node that, Context context) {
	return that.semanticMain(context);
}

Expression semanticImpl(Parser.Forall that, Context context) {
	auto previous = context.locals;
	assert(context.rigidContext);
	foreach (binding; that.bindings) {

		auto rigidity = [context.rigidContext: make!RigidVariable(binding.name)].fromAALiteral;
		auto constraints = binding.constraints
			.map!(a => semanticConstraint(a, context))
			.array
			.map!(a => tuple(a.id, a))
			.rangeToMap;
		auto variable = freshTypeVariable(context, that.position, constraints, rigidity, binding.name);
		context.bindTypeVariable(variable, that.position, false);
	}

	auto value = semanticMain(that.value, context);

	context.locals = previous;
	return value;
}

Expression semanticImpl(Parser.ConstraintTuple that, Context context) {
	auto type = semanticType(that.type, context);
	return make!PredicateTuple(that.index, type);
}

Expression semanticImpl(Parser.Variable that, Context context) {
	auto variable = context.search(that.name, that.position);
	check(!(variable is null), "Undefined variable", that.position);
	return variable;
}

Expression semanticImpl(Parser.Import that, Context context) {
	auto semanticModule = readSemanticModule(that.value.get);
	return make!Import(semanticModule);
}

Expression semanticImpl(Parser.UseSymbol that, Context context) {
	auto value = semanticMain(that.value, context);
	auto Import = value.castTo!Import.mod;
	check(Import, "scope resolution expect an import", that.position);
	check(that.index in Import.aliases, "Undefined variable", that.position);
	return context.unpackModuleDefinition(Import.aliases[that.index](context.recursionCheck), that.position);
}

Type typeStructFrom(T...)(T types) {
	static if (types.length == 0) {
		return make!TypeStruct(emptyArray!Type);
	} else {
		return make!TypeStruct([types[0].convert!Type, types[1 .. $]]);
	}
}

Expression semanticImpl(Parser.TypeTuple that, Context context) {
	auto types = that.values.map!(a => semanticType(a, context)).array;
	return make!TypeStruct(types);
}

Expression semanticImpl(Parser.Postfix!"(*)" that, Context context) {
	auto value = semanticType(that.value, context);
	return make!TypePointer(value);
}

Expression semanticImpl(Parser.Postfix!"[*]" that, Context context) {
	auto value = semanticType(that.value, context);
	return make!TypeArray(value);
}

Expression semanticImpl(Parser.Postfix!"(!)" that, Context context) {
	auto value = semanticType(that.value, context);
	return make!TypeOwnPointer(value);
}

Expression semanticImpl(Parser.Postfix!"[!]" that, Context context) {
	auto value = semanticType(that.value, context);
	return make!TypeOwnArray(value);
}

Expression semanticImpl(Parser.IntLit that, Context context) {
	auto variable = context.freshTypeVariable(that.position, make!PredicateNumber.constraintsFrom);
	return make!IntLit(variable, that.value);
}

Expression semanticImpl(Parser.CharLit that, Context context) {
	return make!CharLit(make!TypeChar(), that.value);
}

Expression semanticImpl(Parser.TupleLit that, Context context) {
	auto values = that.values.map!(a => semanticExpression(a, context)).array;
	return make!TupleLit(make!TypeStruct(values.map!(a => a.type).array), values);
}

Expression semanticImpl(Parser.If that, Context context) {
	auto cond = semanticExpression(that.cond, context);

	auto initial = context.uses;

	context.uses = context.uses.mapValues!(_ => Linearity.unused);
	auto yes = semanticExpression(that.yes, context);
	auto yesUses = context.uses;

	context.uses = context.uses.mapValues!(_ => Linearity.unused);
	auto no = semanticExpression(that.no, context);
	auto noUses = context.uses;

	context.uses = mergeMaps!both(initial, mergeMaps!branch(yesUses, noUses));

	context.typeCheck(cond.type, make!TypeBool(), that.cond.position);
	context.typeCheck(yes.type, no.type, that.position);
	return make!If(yes.type, cond, yes, no);
}

Expression semanticImpl(Parser.Infer that, Context context) {
	auto argumentType = semanticType(that.type, context);
	auto value = semanticExpression(that.value, context);
	context.typeCheck(argumentType, value.type, that.position);
	return value;
}

Expression semanticImpl(Parser.Index that, Context context) {
	auto array = semanticExpression(that.array, context);
	auto index = semanticExpression(that.index, context);

	auto variable = context.freshTypeVariable(that.position);
	auto type = make!TypeFunction(variable, typeStructFrom(make!TypeArray(variable), make!TypeInt(0, false)));
	return semanticCall(make!(Desugar!"index")(type), [array, index], that.position, context);
}

Expression semanticImpl(Parser.TupleIndex that, Context context) {
	auto tuple = semanticExpression(that.tuple, context);
	auto index = that.index;

	auto returnType = context.freshTypeVariable(that.position);
	auto argumentType = context.freshTypeVariable(that.position, constraintsFrom(make!PredicateTuple(that.index, returnType), make!PredicateUnrestricted));
	auto type = make!TypeFunction(returnType, argumentType);
	return semanticCall(make!TupleIndex(type, index), tuple, that.position, context);
}

Expression semanticImpl(Parser.TupleIndexAddress that, Context context) {
	auto tuple = semanticExpression(that.tuple, context);
	auto index = that.index;

	auto variable1 = context.freshTypeVariable(that.position);
	auto variable0 = context.freshTypeVariable(that.position, make!PredicateTuple(that.index, variable1).constraintsFrom);
	auto type = make!TypeFunction(make!TypePointer(variable1), make!TypePointer(variable0));
	return semanticCall(make!TupleIndexAddress(type, index, variable0), tuple, that.position, context);
}

Term semanticCall(Term calle, Term argument, Position position, Context context) {
	auto variable = context.freshTypeVariable(position);
	context.typeCheck(calle.type, make!TypeFunction(variable, argument.type), position);
	return make!Call(variable, calle, argument);
}

Term semanticCall(Term calle, Term[] arguments, Position position, Context context) {
	auto type = make!TypeStruct(arguments.map!(a => a.type).array);
	auto tuple = make!TupleLit(type, arguments);
	return semanticCall(calle, tuple, position, context);
}

Expression semanticImpl(Parser.Call that, Context context) {
	auto calle = semanticExpression(that.calle, context);
	auto argument = semanticExpression(that.argument, context);
	return semanticCall(calle, argument, that.position, context);
}

Expression semanticImpl(Parser.Slice that, Context context) {
	auto array = semanticExpression(that.array, context);
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);

	auto variable = context.freshTypeVariable(that.position);
	auto type = make!TypeFunction(make!TypeArray(variable), typeStructFrom(make!TypeArray(variable), make!TypeInt(0, false), make!TypeInt(0, false)));
	return semanticCall(make!(Desugar!"slice")(type), [array, left, right], that.position, context);
}

Expression semanticImpl(Parser.Binary!"->" that, Context context) {
	auto left = semanticType(that.left, context);
	auto right = semanticType(that.right, context);
	return make!TypeFunction(right, left);
}

//todo remove me
//wierd compiler bug

alias ParserBinary = Parser.Binary;
alias ParserPrefix = Parser.Prefix;

enum operaterName(string _ : "<=") = "less equal";
enum operaterName(string _ : ">=") = "greater equal";
enum operaterName(string _ : "<") = "less";
enum operaterName(string _ : ">") = "greater";

Expression semanticImpl(string op)(ParserBinary!op that, Context context) if (["<=", ">=", ">", "<"].canFind(op)) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	auto variable = context.freshTypeVariable(that.position, make!PredicateEqual.constraintsFrom);
	auto type = make!TypeFunction(make!TypeBool, typeStructFrom(variable, variable));
	return semanticCall(make!(DesugarContext!(operaterName!op))(type, variable), [left, right], that.position, context);
}

enum operaterName(string _ : "*") = "multiply";
enum operaterName(string _ : "/") = "divide";
enum operaterName(string _ : "%") = "modulus";
enum operaterName(string _ : "+") = "add";
enum operaterName(string _ : "-") = "subtract";

Expression semanticImpl(string op)(ParserBinary!op that, Context context) if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	auto variable = context.freshTypeVariable(that.position, make!PredicateNumber.constraintsFrom);
	auto type = make!TypeFunction(variable, typeStructFrom(variable, variable));
	return semanticCall(make!(DesugarContext!(operaterName!op))(type, variable), [left, right], that.position, context);
}

enum operaterName(string _ : "==") = "equal";
enum operaterName(string _ : "!=") = "not equal";

Expression semanticImpl(string op)(ParserBinary!op that, Context context) if (["==", "!="].canFind(op)) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);
	auto variable = context.freshTypeVariable(that.position, make!PredicateEqual.constraintsFrom);
	auto type = make!TypeFunction(make!TypeBool, typeStructFrom(variable, variable));
	return semanticCall(make!(DesugarContext!(operaterName!op))(type, variable), [left, right], that.position, context);
}

enum operaterName(string _ : "&&") = "and";
enum operaterName(string _ : "||") = "or";

Expression semanticImpl(string op)(ParserBinary!op that, Context context) if (["&&", "||"].canFind(op)) {
	auto left = semanticExpression(that.left, context);
	auto right = semanticExpression(that.right, context);

	auto type = make!TypeFunction(make!TypeBool, typeStructFrom(make!TypeBool, make!TypeBool));
	return semanticCall(make!(Desugar!(operaterName!op))(type), [left, right], that.position, context);
}

Expression semanticImpl(ParserPrefix!"!" that, Context context) {
	auto value = semanticExpression(that.value, context);

	auto type = make!TypeFunction(make!TypeBool, make!TypeBool);
	return semanticCall(make!(Desugar!"not")(type), value, that.position, context);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context) if (op == "-") {
	auto value = semanticExpression(that.value, context);
	auto variable = context.freshTypeVariable(that.position, make!PredicateNumber.constraintsFrom);
	auto type = make!TypeFunction(variable, variable);
	return semanticCall(make!(DesugarContext!"negate")(type, variable), value, that.position, context);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context) if (op == "*") {
	auto value = semanticExpression(that.value, context);

	auto variable = context.freshTypeVariable(that.position, make!PredicateUnrestricted.constraintsFrom);
	auto type = make!TypeFunction(variable, make!TypePointer(variable));
	return semanticCall(make!(Desugar!"derefence")(type), value, that.position, context);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context) if (["+", "/"].canFind(op)) {
	error(op ~ " not supported", that.position);
	return null;
}

Term semanticImpl(Parser.VariableDefinition that, Context context) {
	auto value = semanticExpression(that.value, context);
	auto variable = semanticPattern(that.variable, context);
	context.typeCheck(variable.type, value.type, that.position);
	auto lastSemantic = semanticExpression(that.last, context);
	variable.removeBindings(context, that.position);
	return make!VariableDefinition(lastSemantic.type, variable, value, lastSemantic);
}

void removeBindingsImpl(NamedPattern that, Context context, Position position) {
	context.removeTermVariable(that.argument, position);
}

void removeBindingsImpl(TuplePattern that, Context context, Position position) {
	that.matches.each!(a => a.removeBindings(context, position));
}

Pattern semanticImpl(Parser.NamedArgument that, Context context) {
	auto type = context.freshTypeVariable(that.position);
	auto variable = make!Variable(type, that.name, new VarId);
	context.bindTermVariable(variable, that.position, that.shadow);
	return make!NamedPattern(type, variable);
}

Pattern semanticImpl(Parser.TupleArgument that, Context context) {
	auto matches = that.matches.map!(a => semanticPattern(a, context)).array;
	auto type = make!TypeStruct(matches.map!(a => a.type).array);
	return make!TuplePattern(type, matches);
}

Expression semanticImpl(Parser.FuncLit that, Context context) {
	error("only top level lambda are supported for now", that.position);
	return null;
}

Expression semanticImpl(Parser.StringLit that, Context context) {
	return make!StringLit(make!TypeOwnArray(make!TypeChar()), that.value);
}

Expression semanticImpl(Parser.ArrayLit that, Context context) {
	auto variable = context.freshTypeVariable(that.position, make!PredicateUnrestricted.constraintsFrom);
	auto type = make!TypeOwnArray(variable);
	auto values = that.values.map!(a => semanticExpression(a, context)).array;
	foreach (value; values) {
		context.typeCheck(variable, value.type, that.position);
	}

	return make!ArrayLit(type, values);
}

Expression semanticImpl(Parser.ExternJs that, Context context) {
	auto variable = context.freshTypeVariable(that.position);
	return make!ExternJs(variable, that.name);
}
