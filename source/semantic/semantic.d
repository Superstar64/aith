/+
	Copyright (C) 2015-2017  Freddy Angel Cubas "Superstar64"
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
module semantic.semantic;
import std.algorithm;
import std.array;
import std.bigint;
import std.conv;
import std.file;
import std.meta;
import std.range;
import std.typecons;

import app : knownSymbols, readSemanticModule, freshId;
import Parser = parser.ast;
import semantic.astimpl;

import misc.nonstrict;
import misc.position;
import misc.container;
import misc.misc;

Module createModule(Parser.Module parser, Module parent) {
	OwnerDictonary!(string, Parser.ModuleVarDef) rawSymbols;
	foreach (symbol; parser.symbols) {
		check(!(symbol.name in rawSymbols), "Symbol already exists", symbol.position);
		rawSymbols.insert(symbol.name, symbol);
	}
	auto rawSymbolsFrozen = rawSymbols.freeze;
	ModuleDefinition delegate(RecursionChecker) resolveSymbolThunk(Parser.ModuleVarDef symbol) {
		ModuleDefinition thunk(RecursionChecker recursionCheck) {
			return resolveSymbol(rawSymbolsFrozen, symbol, parent, recursionCheck);
		}

		return &thunk;
	}

	OwnerDictonary!(string, ModuleDefinition delegate(RecursionChecker)) aliases;
	ModuleDefinition delegate(RecursionChecker)[] orderedAliases;
	foreach (symbol; parser.symbols) {
		auto value = resolveSymbolThunk(symbol);
		orderedAliases ~= value;
		aliases.insert(symbol.name, value);
	}
	auto ret = new Module;
	ret.orderedAliases = orderedAliases;
	ret.aliases = aliases.freeze;
	return ret;
}

void validateModule(Module mod) {
	foreach (symbol; mod.orderedAliases) {
		symbol(RecursionChecker());
	}
}

Expression unpackModuleDefinition(Context context, ModuleDefinition resolved, Position position) {
	if (auto term = resolved.matrix.castTo!Term) {
		auto freshStage = resolved.stagePrefix.range.map!(a => item(a.key, context.freshStageVariable(position).convert!Stage)).cache.rangeToMap;
		auto freshType = resolved.typePrefix.range.map!(a => item(a.key, context.freshTypeVariable(a.value.type.substitute(freshStage), position).convert!Type)).cache.rangeToMap;

		foreach (variable, requirement; resolved.typePrefix) {
			foreach (id, predicate; requirement.predicates) {
				context.predicateCheck(predicate.substitute(freshType).substitute(freshStage), freshType[variable].substitute(freshStage), position);
			}
		}

		return term.substitute(freshType).substitute(freshStage);
	} else {
		return resolved.matrix;
	}
}

ModuleDefinition resolveSymbol(Dictonary!(string, Parser.ModuleVarDef) rawSymbols, Parser.ModuleVarDef symbol, Module parent, RecursionChecker recursionCheck) {
	bool known = symbol in knownSymbols;
	bool disallowed = symbol in recursionCheck.disallowed;
	// todo think about relation between recursive and intermediate
	bool recursive = symbol in recursionCheck.recursive;
	bool intermediate = recursionCheck.frame && symbol in recursionCheck.frame.typeChecker.bindingGroup;
	if (known) {
		assert(!recursive && !disallowed && !intermediate);
		return knownSymbols[symbol];
	} else if (disallowed) {
		assert(!known && !recursive && !intermediate);
		error("Illegal self reference", symbol.position);
		assert(0);
	} else if (intermediate) {
		assert(!known && !disallowed);
		return ModuleDefinition(recursionCheck.frame.typeChecker.bindingGroup[symbol]);
	} else if (recursive) {
		assert(!known && !disallowed);
		auto frame = recursionCheck.recursive[symbol];
		frame.unifyTypeCheckers;
		auto checker = frame.typeChecker;
		assert(symbol in checker.bindingGroup);
		return ModuleDefinition(checker.bindingGroup[symbol]);
	} else {
		bool referenced = semanticGlobal(rawSymbols, symbol, parent, recursionCheck);
		if (referenced) {
			return ModuleDefinition(recursionCheck.frame.typeChecker.bindingGroup[symbol]);
		} else {
			return knownSymbols[symbol];
		}
	}
}

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

	Dictonary!(TypeVariableId, TypeRequirement) freshTypeVariables;
	TypeAlgebra[] typeChecks;
	Dictonary!(RigidVariableId, RigidRequirement) freshRigidVariables;

	Dictonary!(StageVariableId, StageRequirement) freshStageVariables;
	StageAlgebra[] stageChecks;

	Dictonary!(SymbolId, Term delegate(Type delegate(Parser.ModuleVarDef), Dictonary!(TypeVariableId, TypeRequirement))) forwardReplacements;

}

// todo remove code duplication
Requirement mapPredicates(alias f, Requirement)(Requirement requirement) {
	requirement.predicates = f(requirement.predicates);
	return requirement;
}

void removeRigidity(TypeSystem typeSystem) {
	foreach (id, requirement; typeSystem.unsolvedRigid) {
		auto fresh = freshId!TypeVariableId;
		auto substitution = singletonMap(id, make!TypeVariable(requirement.type, fresh).convert!Type);
		assert(typeSystem.algebra.length == 0);
		typeSystem.substitution = typeSystem.substitution.substitute(substitution);
		typeSystem.substitutionRigid = typeSystem.substitutionRigid.substitute(substitution);
		typeSystem.substitutionRigid = typeSystem.substitutionRigid.insertCopy(id, make!TypeVariable(requirement.type, fresh));
		typeSystem.unsolved = typeSystem.unsolved.insertCopy(fresh, TypeRequirement(requirement.position, requirement.type, requirement.predicates));
		typeSystem.unsolvedRigid = typeSystem.unsolvedRigid.removeCopy(id);
	}
	typeSystem.unsolved = typeSystem.unsolved.mapValues!(requirement => requirement.mapPredicates!(predicates => predicates.substitute(typeSystem.substitutionRigid)));
}

void evaluateTypeChecks(TypeChecker typeChecker) {
	auto stageSystem = new StageSystem(typeChecker.stageChecks, typeChecker.freshStageVariables);
	auto typeSystem = new TypeSystem(typeChecker.typeChecks, typeChecker.freshTypeVariables, typeChecker.freshRigidVariables, stageSystem);
	unifyAll(typeSystem);

	removeRigidity(typeSystem);

	auto freeGroup = typeChecker.bindingGroup
		.byValue
		.map!(a => a.type)
		.map!(a => a.substitute(typeSystem.substitution).substitute(typeSystem.substitutionRigid))
		.map!freeVariables;
	auto free = freeGroup.front;

	assert(freeGroup.all!(a => isSubSet(free, a) && isSubSet(a, free)));

	foreach (id, unsolved; typeSystem.unsolved) {
		if (!(id in free)) {
			error("Unable to infer type variable", unsolved.position);
		}
	}

	unifyAll(stageSystem);
	auto stageFreeGroup = typeChecker.bindingGroup
		.byValue
		.map!(a => a.type.type)
		.map!(a => a.substitute(stageSystem.substitution))
		.map!freeVariables;
	auto stageFree = stageFreeGroup.front;
	assert(stageFreeGroup.all!(a => isSubSet(stageFree, a) && isSubSet(a, stageFree)));

	foreach (id, requirement; stageSystem.unsolved) {
		if (!(id in stageFree)) {
			error("Unable to infer stage variable", requirement.position);
		}
	}
	typeSystem.unsolved = typeSystem.unsolved.substitute(stageSystem.substitution);
	typeSystem.unsolvedRigid = typeSystem.unsolvedRigid.substitute(stageSystem.substitution);

	Lazy!(Dictonary!(SymbolId, Term)) forward;
	Term substituteAll(Term that) {
		return that.substitute(typeSystem.substitution).substitute(typeSystem.substitutionRigid).substitute(stageSystem.substitution).substitute(forward).reduceMacros;
	}

	Type symbolType(Parser.ModuleVarDef def) {
		return typeChecker.bindingGroup[def].type.substitute(typeSystem.substitution).substitute(typeSystem.substitutionRigid).substitute(stageSystem.substitution);
	}

	Dictonary!(SymbolId, Term) forwardImpl() {
		return typeChecker.forwardReplacements.mapValues!(a => substituteAll(a(&symbolType, typeSystem.unsolved)));
	}

	forward = defer(&forwardImpl);

	foreach (symbol, expression0; typeChecker.bindingGroup) {
		auto expression1 = substituteAll(expression0);
		knownSymbols.insert(symbol, ModuleDefinition(expression1, typeSystem.unsolved, stageSystem.unsolved));
		if (symbol.sort == Parser.SymbolSort.symbol) {
			check(expression1.type.freeVariables.length == 0, "Strong symbols cannot be generic", symbol.position);
		}
	}
}

void moveTypeChecker(TypeChecker from, TypeChecker to) {
	if (from is to) {
		return;
	}
	to.bindingGroup = mergeMapsUnique(to.bindingGroup, from.bindingGroup);
	to.freshTypeVariables = mergeMapsUnique(to.freshTypeVariables, from.freshTypeVariables);
	to.typeChecks = to.typeChecks ~ from.typeChecks;
	to.freshStageVariables = mergeMapsUnique(to.freshStageVariables, from.freshStageVariables);
	to.freshRigidVariables = mergeMapsUnique(to.freshRigidVariables, from.freshRigidVariables);
	to.stageChecks = to.stageChecks ~ from.stageChecks;
	to.forwardReplacements = mergeMapsUnique(to.forwardReplacements, from.forwardReplacements);
}

struct RecursionChecker {
	TypeCheckerFrame* frame;
	Dictonary!(Parser.ModuleVarDef, TypeCheckerFrame*) recursive;
	Set!(Parser.ModuleVarDef) disallowed;
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
	RigidContextId rigidContext;
	RecursionChecker recursionCheck;
	Module parent; // nullable

	// mutable data
	TypeChecker typeChecker;
	Dictonary!(string, Expression[]) locals;
	Dictonary!(VariableId, Linearity) uses;
	Term delegate(Term) doBlock; // nullable

	this(Dictonary!(string, Parser.ModuleVarDef) rawGlobalSymbols, RecursionChecker recursionCheck, Module parent) {
		this.rawGlobalSymbols = rawGlobalSymbols;
		this.rigidContext = freshId!RigidContextId;
		this.typeChecker = new TypeChecker;
		recursionCheck.frame.typeChecker = &typeChecker;
		this.recursionCheck = recursionCheck;
		this.parent = parent;
	}

	TypeVariable freshTypeVariable(Stage type, Position position) {
		auto id = freshId!TypeVariableId;
		typeChecker.freshTypeVariables = typeChecker.freshTypeVariables.insertCopy(id, TypeRequirement(position, type));
		auto result = make!TypeVariable(type, id);
		return result;
	}

	StageVariable freshStageVariable(Position position) {
		auto id = freshId!StageVariableId;
		typeChecker.freshStageVariables = typeChecker.freshStageVariables.insertCopy(id, StageRequirement(position));
		auto result = make!StageVariable(id);
		return result;
	}

	void typeCheck(Type left, Type right, Position position) {
		typeChecker.typeChecks ~= equation(left, right, position);
	}

	void predicateCheck(Predicate predicate, Type type, Position position) {
		typeChecker.typeChecks ~= predicateCall(predicate, type, position);
	}

	void stageCheck(Stage left, Stage right, Position position) {
		typeChecker.stageChecks ~= equation(left, right, position);
	}

	void bindTypeVariable(Type variable, string name, Position position, bool duplicate) {
		locals = locals.insertIfMissing(name, emptyArray!Expression);

		if (!duplicate && locals[name].length != 0) {
			error("duplicate name", position);
		}
		locals = locals.replaceCopy(name, locals[name] ~ variable);
	}

	void bindTermVariable(Variable variable, Position position, bool duplicate) {
		locals = locals.insertIfMissing(variable.name, emptyArray!Expression);

		if (!duplicate && locals[variable.name].length != 0) {
			error("duplicate name", position);
		}
		locals = locals.replaceCopy(variable.name, locals[variable.name] ~ variable);
		uses = uses.insertCopy(variable.id, Linearity.unused);
	}

	void removeTermVariable(Variable variable, Position position) {
		if (uses[variable.id] != Linearity.linear) {
			this.predicateCheck(make!PredicateUnrestricted, variable.type, position);
		}
		locals = locals.replaceCopy(variable.name, locals[variable.name][0 .. $ - 1]);
		uses = uses.removeCopy(variable.id);
	}
}

Expression search(Context context, string name, Position position) {
	if (name in context.locals && context.locals[name].length > 0) {
		if (auto variable = context.locals[name][$ - 1].castTo!Variable) {
			assert(variable.id in context.uses);
			context.uses = context.uses.replaceCopy(variable.id, context.uses[variable.id].use);
		}
		return context.locals[name][$ - 1];
	}
	return searchGlobal(context, name, position);
}

Expression searchGlobal(Context context, string name, Position position) {
	static foreach (built; builtins) {
		if (name == built) {
			return context.unpackModuleDefinition(builtin!built, position);
		}
	}
	if (name in context.rawGlobalSymbols) {
		auto symbol = context.rawGlobalSymbols[name];
		auto resolved = resolveSymbol(context.rawGlobalSymbols, symbol, context.parent, context.recursionCheck);
		return context.unpackModuleDefinition(resolved, position);
	} else if (context.parent) {
		if (name in context.parent.aliases) {
			auto symbol = context.parent.aliases[name](context.recursionCheck);
			return context.unpackModuleDefinition(symbol, position);
		} else {
			return null;
		}
	} else {
		return null;
	}
}

Term semanticDesugar(string name)(Context context, Position position, Term argument) {
	auto builtin = searchGlobal(context, "desugar " ~ name, position);
	check(builtin, "Can't resolve builtin " ~ name, position);
	return semanticMacro(assumeTerm(builtin, position), argument, position, context);
}

Term semanticDesugar(string name)(Context context, Position position, Term[] arguments) {
	auto builtin = searchGlobal(context, "desugar " ~ name, position);
	check(builtin, "Can't resolve builtin " ~ name, position);
	Term current = assumeTerm(builtin, position);
	foreach (argument; arguments) {
		current = semanticMacro(current, argument, position, context);
	}
	return current;
}

TypeVariableId[] freeVariablesOrderedUnique(Type that) {
	TypeVariableId[] original = that.freeVariablesOrdered;
	Set!TypeVariableId unique;
	TypeVariableId[] result;
	foreach (variable; original) {
		if (!(variable in unique)) {
			unique = unique.insertCopy(variable);
			result ~= variable;
		}
	}
	return result;
}

Tuple!(Type, Predicate)[] dictonaryOf(Type that, Dictonary!(TypeVariableId, TypeRequirement) requirements) {
	return that.freeVariablesOrderedUnique.map!(a => requirements[a].predicates
			.byValue
			.array
			.sort!((a, b) => a.compare(b))
			.map!(b => tuple(make!TypeVariable(requirements[a].type, a).convert!Type, b))).joiner.array;
}

bool semanticGlobal(Dictonary!(string, Parser.ModuleVarDef) parserGlobals, Parser.ModuleVarDef symbol, Module parent, RecursionChecker recursionCheck) {
	assert(!(symbol in recursionCheck.recursive) && !(symbol in recursionCheck.disallowed));

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
	// graphs of the form (inline -> symbol -> inline) need to throw away work and
	// be transformed into (symbol -> inline -> symbol)

	if (symbol.sort == Parser.SymbolSort.inline) {
		auto disallowed = recursionCheck.disallowed.insertCopy(symbol);
		auto recursive = recursionCheck.recursive;
		auto checker = RecursionChecker(&frame, recursive, disallowed);
		auto context = new Context(parserGlobals, checker, parent);
		Term term = semanticTerm(symbol.value, context);
		if (symbol in knownSymbols) {
			// throw away work
			return false;
		}
		if (symbol.explicitType) {
			context.typeCheck(term.type, symbol.explicitType.semanticType(context), symbol.position);
		}

		assert(!(symbol in context.typeChecker.bindingGroup));
		context.typeChecker.bindingGroup = context.typeChecker.bindingGroup.insertCopy(symbol, term);

		assert(!frame.referenced);
		context.typeChecker.evaluateTypeChecks;
		return false;
	} else if (symbol.sort == Parser.SymbolSort.external) {
		auto disallowed = recursionCheck.disallowed.insertCopy(symbol);
		auto recursive = recursionCheck.recursive;
		auto checker = RecursionChecker(&frame, recursive, disallowed);
		auto context = new Context(parserGlobals, checker, parent);
		check(!!symbol.explicitType, "Extern expect a type", symbol.position);
		auto external = symbol.value.castTo!(Parser.ExternJs);
		check(!!external, "External global expects external term", symbol.position);
		auto term = semanticExtern(external, symbol.explicitType, context);
		assert(!(symbol in context.typeChecker.bindingGroup));
		context.typeChecker.bindingGroup = context.typeChecker.bindingGroup.insertCopy(symbol, term);

		assert(!frame.referenced);
		context.typeChecker.evaluateTypeChecks;
		return false;
	} else {
		// remove inlines from disallowed stack
		auto disallowed = emptySet!(Parser.ModuleVarDef);
		auto recursive = recursionCheck.recursive.insertCopy(symbol, &frame);
		auto checker = RecursionChecker(&frame, recursive, disallowed);
		auto context = new Context(parserGlobals, checker, parent);

		Tuple!(Type, Predicate)[] dictonaries;

		auto strong = symbol.sort == Parser.SymbolSort.symbol;
		auto argument = context.freshTypeVariable(make!StageRuntime, symbol.position);
		auto result = context.freshTypeVariable(make!StageRuntime, symbol.position);
		auto expectedType = make!TypeFunction(make!StageRuntime, result, argument);

		if (symbol.explicitType) {
			auto items = semanticScheme(symbol.explicitType, context);
			context.typeCheck(expectedType, items[0], symbol.position);
			dictonaries = items[1];
		}
		auto forward = make!SymbolForwardReference(expectedType, freshId!SymbolId);
		assert(!(symbol in context.typeChecker.bindingGroup));
		context.typeChecker.bindingGroup = context.typeChecker.bindingGroup.insertCopy(symbol, forward);

		auto internalType = make!TypeMacro(make!StageMacro(result.type, argument.type), result, argument);
		auto internal = semanticTerm(symbol.value, context);
		context.typeCheck(internalType, internal.type, symbol.position);

		Term makeReplacement(Type delegate(Parser.ModuleVarDef) symbolType, Dictonary!(TypeVariableId, TypeRequirement) requirements) {
			auto type = symbolType(symbol);
			auto linkage = strong ? Linkage.strong : Linkage.weak;
			return make!SymbolReference(expectedType, symbol.name, linkage, freshId!SymbolId, eager(internal), type.dictonaryOf(requirements));
		}

		assert(!(forward.id in context.typeChecker.forwardReplacements));
		context.typeChecker.forwardReplacements = context.typeChecker.forwardReplacements.insertCopy(forward.id, &makeReplacement);
		if (frame.referenced) {
			return true;
		} else {
			context.typeChecker.evaluateTypeChecks;
			return false;
		}
	}
}

Term semanticExtern(Parser.ExternJs that, Parser.Expression annotation, Context context) {
	auto items = semanticScheme(annotation, context);
	auto dictonaries = items[1];
	context.stageCheck(items[0].type, make!StageRuntime, that.position);
	return make!ExternJs(items[0], that.name, dictonaries);
}

Tuple!(Type, Tuple!(Type, Predicate)[]) semanticScheme(Parser.Expression that, Context context) {
	if (auto forall = that.castTo!(Parser.Forall)) {
		return semanticForall(forall, context);
	} else {
		return tuple(semanticType(that, context), emptyArray!(Tuple!(Type, Predicate)));
	}
}

Type freshRigidTypeVariable(Context context, string name, Dictonary!(PredicateId, Predicate) predicates, Position position) {
	auto stage = context.freshStageVariable(position);
	auto id = freshId!RigidVariableId;
	auto var = make!TypeVariableRigid(stage, id, name, context.rigidContext);
	context.typeChecker.freshRigidVariables = context.typeChecker.freshRigidVariables.insertCopy(id, RigidRequirement(position, stage, predicates));
	return var;
}

Tuple!(Type, Tuple!(Type, Predicate)[]) semanticForall(Parser.Forall that, Context context) {
	auto previous = context.locals;
	Tuple!(Type, Predicate)[] dictonaries;
	foreach (binding; that.bindings) {
		auto predicates = binding.predicates
			.map!(a => semanticConstraint(a, context))
			.cache
			.map!(a => item(a.id, a))
			.rangeToMap;
		auto variable = freshRigidTypeVariable(context, binding.name, predicates, that.position);
		dictonaries ~= predicates.byValue.map!(a => tuple(variable.convert!Type, a)).array;
		context.bindTypeVariable(variable, binding.name, that.position, false);
	}

	auto value = semanticType(that.value, context);

	context.locals = previous;
	return tuple(value, dictonaries);
}

Expression semanticImpl(Parser.Forall that, Context context) {
	return semanticForall(that, context)[0];
}

Expression builtinImpl(string name : "true")() {
	return make!BoolLit(make!TypeBool(make!StageRuntime), true);
}

Expression builtinImpl(string name : "false")() {
	return make!BoolLit(make!TypeBool(make!StageRuntime), false);
}

Expression builtinImpl(string name : "boolean")() {
	return make!TypeBool(make!StageRuntime);
}

Expression builtinImpl(string name : "character")() {
	return make!TypeChar(make!StageRuntime);
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
	return make!TypeWorld(make!StageRuntime);
}

Expression builtinImpl(string name : "integer")() {
	return make!TypeInt(make!StageRuntime, 0, true);
}

Expression builtinImpl(string name : "integer8")() {
	return make!TypeInt(make!StageRuntime, 8, true);
}

Expression builtinImpl(string name : "integer16")() {
	return make!TypeInt(make!StageRuntime, 16, true);
}

Expression builtinImpl(string name : "integer32")() {
	return make!TypeInt(make!StageRuntime, 32, true);
}

Expression builtinImpl(string name : "integer64")() {
	return make!TypeInt(make!StageRuntime, 64, true);
}

Expression builtinImpl(string name : "natural")() {
	return make!TypeInt(make!StageRuntime, 0, false);
}

Expression builtinImpl(string name : "natural8")() {
	return make!TypeInt(make!StageRuntime, 8, false);
}

Expression builtinImpl(string name : "natural16")() {
	return make!TypeInt(make!StageRuntime, 16, false);
}

Expression builtinImpl(string name : "natural32")() {
	return make!TypeInt(make!StageRuntime, 32, false);
}

Expression builtinImpl(string name : "natural64")() {
	return make!TypeInt(make!StageRuntime, 64, false);
}

ModuleDefinition builtin(string name)() {
	return ModuleDefinition(builtinImpl!name);
}

enum builtins = AliasSeq!("true", "false", "boolean", "character", "equal", "number", "unrestricted", "world", "integer", "integer8", "integer16", "integer32", "integer64", "natural", "natural8", "natural16", "natural32", "natural64");

Dictonary!(PredicateId, Predicate) predicatesFrom(Predicate predicate) {
	return singletonMap(predicate.id, predicate);
}

Dictonary!(PredicateId, Predicate) predicatesFrom(T...)(Predicate predicate, T tail) {
	return predicatesFrom(tail).insertCopy(predicate.id, predicate);
}

Type assumeType(Expression value, Position position, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!Type, "Expected type", position, file, line);
	return value.castTo!Type;
}

Type assumeTypeRuntime(Expression value, Context context, Position position, string file = __FILE__, int line = __LINE__) {
	auto type = assumeType(value, position, file, line);
	context.stageCheck(type.type, make!StageRuntime, position);
	return type;
}

Predicate assumeConstraint(Expression value, Position position, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!Predicate, "Expected constraint", position, file, line);
	return value.castTo!Predicate;
}

Term assumeRuntime(Expression value, Context context, Position position, string file = __FILE__, int line = __LINE__) {
	auto result = value.assumeTerm(position, file, line);
	context.stageCheck(result.type.type, make!StageRuntime, position);
	return result;
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

Type semanticTypeRuntime(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeTypeRuntime(semanticMain(that, context), context, that.position, file, line);
}

Predicate semanticConstraint(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeConstraint(semanticMain(that, context), that.position, file, line);
}

Term semanticRuntime(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeRuntime(semanticMain(that, context), context, that.position, file, line);
}

Term semanticTerm(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeTerm(semanticMain(that, context), that.position, file, line);
}

Pattern semanticPattern(Parser.Pattern that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumePattern(semanticMain(that, context), that.position, file, line);
}

auto semanticMain(Parser.Node that, Context context) {
	return that.semanticMain(context);
}

Expression semanticImpl(Parser.FunctionLiteral that, Context context) {
	auto argument = semanticPattern(that.argument, context);
	addBindings(argument, that.argument.position, context);
	auto value = semanticTerm(that.text, context);
	auto type = make!TypeMacro(make!StageMacro(value.type.type, argument.type.type), value.type, argument.type);
	removeBindings(argument, that.argument.position, context);
	auto variable = make!Variable(argument.type, "", new VariableId);

	auto definition = make!VariableDefinition(value.type, argument, variable, value);
	return make!MacroFunctionLiteral(type, Argument(variable.id, ""), definition);
}

Expression semanticImpl(Parser.MacroFunctionLiteral that, Context context) {
	auto freshStage = context.freshStageVariable(that.position);
	auto freshType = context.freshTypeVariable(freshStage, that.position);

	auto variable = make!Variable(freshType, that.argument, new VariableId);
	context.bindTermVariable(variable, that.position, that.shadow);

	auto text = semanticTerm(that.text, context);
	auto type = make!TypeMacro(make!StageMacro(text.type.type, variable.type.type), text.type, variable.type);
	return make!MacroFunctionLiteral(type, Argument(variable.id, variable.name), text);
}

Term callRuntime(Context context, Position position) {
	auto a = context.freshTypeVariable(make!StageRuntime, position);
	auto b = context.freshTypeVariable(make!StageRuntime, position);
	auto wrapper = make!Variable(make!TypeFunction(make!StageRuntime, a, b), "f", new VariableId);
	auto argument = make!Variable(a, "a", new VariableId);
	auto apply = make!Call(b, wrapper, argument);
	auto intermediate = make!MacroFunctionLiteral(make!TypeMacro(make!StageMacro(a.type, b.type), a, b), Argument(argument.id, argument.name), apply);
	auto type = make!TypeMacro(make!StageMacro(intermediate.type.type, wrapper.type.type), intermediate.type, wrapper.type);
	return make!MacroFunctionLiteral(type, Argument(wrapper.id, wrapper.name), intermediate);
}

Term semanticCall(Term calle, Term argument, Position position, Context context) {
	auto variable = context.freshTypeVariable(make!StageRuntime, position);
	context.typeCheck(calle.type, make!TypeFunction(make!StageRuntime, variable, argument.type), position);
	return make!Call(variable, calle, argument);
}

Term semanticCall(Term calle, Term[] arguments, Position position, Context context) {
	auto type = make!TypeStruct(make!StageRuntime, arguments.map!(a => a.type).array);
	auto tuple = make!TupleLit(type, arguments);
	return semanticCall(calle, tuple, position, context);
}

Expression semanticImpl(Parser.Call that, Context context) {
	auto calle = semanticTerm(that.calle, context);
	auto argument = semanticTerm(that.argument, context);
	return semanticMacro(calle, argument, that.position, context);
}

Expression semanticImpl(Parser.FromRuntime that, Context context) {
	auto value = semanticTerm(that.value, context);
	return semanticMacro(callRuntime(context, that.position), value, that.position, context);
}

Term semanticMacro(Term calle, Term argument, Position position, Context context) {
	auto freshStage = context.freshStageVariable(position);
	auto freshType = context.freshTypeVariable(freshStage, position);
	auto type = make!TypeMacro(make!StageMacro(freshType.type, argument.type.type), freshType, argument.type);
	context.typeCheck(type, calle.type, position);

	return make!MacroCall(freshType, calle, argument);
}

Expression semanticImpl(Parser.Do that, Context context) {
	auto previous = context.doBlock;
	scope (exit) {
		context.doBlock = previous;
	}
	context.doBlock = a => a;
	auto internal = that.value.semanticTerm(context);
	auto effectless = context.semanticDesugar!"pure"(that.position, internal);
	return context.doBlock(effectless);
}

Term delegate(Term) makeTryClosure(Term internal, Variable variable, Position position, Context context) {
	Term closure(Term dependent) {
		auto type = make!TypeMacro(make!StageMacro(dependent.type.type, variable.type.type), dependent.type, variable.type);
		auto continuation = make!MacroFunctionLiteral(type, Argument(variable.id, variable.name), dependent);
		return context.semanticDesugar!"bind"(position, [internal, continuation]);
	}

	return &closure;
}

Term semanticTry(Term internal, Position position, Context context) {
	auto id = new VariableId();
	auto stage = context.freshStageVariable(position);
	auto type = context.freshTypeVariable(stage, position);

	auto variable = make!Variable(type, "", id);

	auto outer = context.doBlock;
	auto inner = makeTryClosure(internal, variable, position, context);
	context.doBlock = dependent => outer(inner(dependent));
	return variable;
}

Expression semanticImpl(Parser.Try that, Context context) {
	check(context.doBlock, "Expected do block for try", that.position);
	auto internal = semanticTerm(that.value, context);
	return semanticTry(internal, that.position, context);
}

Term delegate(Term) makeVariableDefinitionBinder(Term value, Pattern variable, Position position, Context context) {
	Term closure(Term dependent) {
		auto id = new VariableId();
		auto stage = context.freshStageVariable(position);
		auto type = context.freshTypeVariable(stage, position);

		auto os = make!Variable(type, "os", id);

		auto term = semanticMacro(dependent, os, position, context);
		auto definition = make!VariableDefinition(term.type, variable, value, term);
		auto wtype = make!TypeMacro(make!StageMacro(definition.type.type, os.type.type), definition.type, os.type);
		auto wrapper = make!MacroFunctionLiteral(wtype, Argument(os.id, os.name), definition);
		return wrapper;
	}

	return &closure;
}

Term semanticImpl(Parser.VariableDefinition that, Context context) {
	auto value = semanticRuntime(that.value, context);
	auto variable = semanticPattern(that.variable, context);
	context.typeCheck(variable.type, value.type, that.position);
	addBindings(variable, that.variable.position, context);
	auto varDo = context.doBlock;
	if (context.doBlock) {
		context.doBlock = a => a;
	}

	auto last = semanticTerm(that.last, context);
	removeBindings(variable, that.variable.position, context);
	auto valDo = context.doBlock;
	if (context.doBlock) {
		assert(varDo);
		auto binder = makeVariableDefinitionBinder(value, variable, that.position, context);
		context.doBlock = dependent => varDo(binder(valDo(dependent)));
		return last;
	} else {
		return make!VariableDefinition(last.type, variable, value, last);
	}
}

Term semanticImpl(Parser.Run that, Context context) {
	check(context.doBlock, "run without do block", that.position);

	auto value = semanticTry(semanticTerm(that.value, context), that.position, context);
	auto variable = make!TuplePattern(typeStructFrom(), emptyArray!Pattern);
	context.typeCheck(variable.type, value.type, that.position);
	auto varDo = context.doBlock;
	context.doBlock = a => a;

	auto last = semanticRuntime(that.last, context);
	auto valDo = context.doBlock;

	auto binder = makeVariableDefinitionBinder(value, variable, that.position, context);
	context.doBlock = dependent => varDo(binder(valDo(dependent)));
	return last;
}

void addBindings(Pattern variable, Position position, Context context) {
	foreach (binding; variable.orderedBindings) {
		context.bindTermVariable(binding[0], position, binding[1]);
	}
}

void removeBindings(Pattern variable, Position position, Context context) {
	foreach (binding; variable.orderedBindings) {
		context.removeTermVariable(binding[0], position);
	}
}

Pattern semanticImpl(Parser.NamedArgument that, Context context) {
	auto type = context.freshTypeVariable(make!StageRuntime, that.position);
	return make!NamedPattern(type, new VariableId, that.name, that.shadow);
}

Pattern semanticImpl(Parser.TupleArgument that, Context context) {
	auto matches = that.matches.map!(a => semanticPattern(a, context)).cache.array;
	auto type = make!TypeStruct(make!StageRuntime, matches.map!(a => a.type).array);
	return make!TuplePattern(type, matches);
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
		return make!TypeStruct(make!StageRuntime, emptyArray!Type);
	} else {
		return make!TypeStruct(make!StageRuntime, [types[0].convert!Type, types[1 .. $]]);
	}
}

Expression semanticImpl(Parser.TypeTuple that, Context context) {
	auto types = that.values.map!(a => semanticTypeRuntime(a, context)).cache.array;
	return make!TypeStruct(make!StageRuntime, types);
}

Expression semanticImpl(Parser.TypePointer!"raw" that, Context context) {
	auto value = semanticTypeRuntime(that.value, context);
	return make!TypePointer(make!StageRuntime, value);
}

Expression semanticImpl(Parser.TypeArray!"raw" that, Context context) {
	auto value = semanticTypeRuntime(that.value, context);
	return make!TypeArray(make!StageRuntime, value);
}

Expression semanticImpl(Parser.TypePointer!"unique" that, Context context) {
	auto value = semanticTypeRuntime(that.value, context);
	return make!TypeOwnPointer(make!StageRuntime, value);
}

Expression semanticImpl(Parser.TypeArray!"unique" that, Context context) {
	auto value = semanticTypeRuntime(that.value, context);
	return make!TypeOwnArray(make!StageRuntime, value);
}

Expression semanticImpl(Parser.IntLit that, Context context) {
	auto variable = context.freshTypeVariable(make!StageRuntime, that.position);
	context.predicateCheck(make!PredicateNumber, variable, that.position);
	return make!IntLit(variable, that.value);
}

Expression semanticImpl(Parser.CharLit that, Context context) {
	return make!CharLit(make!TypeChar(make!StageRuntime), that.value);
}

Expression semanticImpl(Parser.TupleLit that, Context context) {
	auto values = that.values.map!(a => semanticRuntime(a, context)).cache.array;
	return make!TupleLit(make!TypeStruct(make!StageRuntime, values.map!(a => a.type).array), values);
}

Expression semanticImpl(Parser.If that, Context context) {
	auto cond = semanticRuntime(that.cond, context);

	auto initial = context.uses;

	context.uses = context.uses.mapValues!(_ => Linearity.unused);
	auto yes = semanticRuntime(that.yes, context);
	auto yesUses = context.uses;

	context.uses = context.uses.mapValues!(_ => Linearity.unused);
	auto no = semanticRuntime(that.no, context);
	auto noUses = context.uses;

	context.uses = mergeMaps!both(initial, mergeMaps!branch(yesUses, noUses));

	context.typeCheck(cond.type, make!TypeBool(make!StageRuntime), that.cond.position);
	context.typeCheck(yes.type, no.type, that.position);
	return make!If(yes.type, cond, yes, no);
}

Expression semanticImpl(Parser.Infer that, Context context) {
	auto argumentType = semanticType(that.type, context);
	auto value = semanticRuntime(that.value, context);
	context.typeCheck(argumentType, value.type, that.position);
	return value;
}

Expression semanticImpl(Parser.Index that, Context context) {
	auto array = semanticRuntime(that.array, context);
	auto index = semanticRuntime(that.index, context);
	return context.semanticDesugar!"index"(that.position, [array, index]);
}

Expression semanticImpl(Parser.IndexAddress that, Context context) {
	auto array = semanticRuntime(that.array, context);
	auto index = semanticRuntime(that.index, context);
	return context.semanticDesugar!"index address"(that.position, [array, index]);
}

Expression semanticImpl(Parser.Binary!"<-" that, Context context) {
	auto pointer = semanticRuntime(that.left, context);
	auto target = semanticRuntime(that.right, context);
	return context.semanticDesugar!"assign"(that.position, [pointer, target]);
}

Expression semanticImpl(Parser.TupleIndex that, Context context) {
	auto tuple = semanticRuntime(that.tuple, context);
	auto index = that.index;

	auto returnType = context.freshTypeVariable(make!StageRuntime, that.position);
	auto argumentType = context.freshTypeVariable(make!StageRuntime, that.position);
	context.predicateCheck(make!PredicateTuple(that.index, returnType), argumentType, that.position);
	auto type = make!TypeFunction(make!StageRuntime, returnType, argumentType);
	return semanticCall(make!TupleIndex(type, index), tuple, that.position, context);
}

Expression semanticImpl(Parser.TupleIndexAddress that, Context context) {
	auto tuple = semanticRuntime(that.tuple, context);
	auto index = that.index;

	auto variable1 = context.freshTypeVariable(make!StageRuntime, that.position);
	auto variable0 = context.freshTypeVariable(make!StageRuntime, that.position);
	context.predicateCheck(make!PredicateTuple(that.index, variable1), variable0, that.position);
	auto type = make!TypeFunction(make!StageRuntime, make!TypePointer(make!StageRuntime, variable1), make!TypePointer(make!StageRuntime, variable0));
	return semanticCall(make!TupleIndexAddress(type, index, variable0), tuple, that.position, context);
}

Expression semanticImpl(Parser.Slice that, Context context) {
	auto array = semanticRuntime(that.array, context);
	auto left = semanticRuntime(that.left, context);
	auto right = semanticRuntime(that.right, context);
	return context.semanticDesugar!"slice"(that.position, [array, left, right]);
}

Expression semanticImpl(Parser.Binary!"->" that, Context context) {
	auto left = semanticTypeRuntime(that.left, context);
	auto right = semanticTypeRuntime(that.right, context);
	return make!TypeFunction(make!StageRuntime, right, left);
}

Expression semanticImpl(Parser.Binary!"~>" that, Context context) {
	auto left = semanticType(that.left, context);
	auto right = semanticType(that.right, context);
	return make!TypeMacro(make!StageMacro(right.type, left.type), right, left);
}

//todo remove me
//wierd compiler bug

alias ParserBinary = Parser.Binary;
alias ParserPrefix = Parser.Prefix;

enum operaterName(string _ : "<=") = "less equal";
enum operaterName(string _ : ">=") = "greater equal";
enum operaterName(string _ : "<") = "less";
enum operaterName(string _ : ">") = "greater";
enum operaterName(string _ : "*") = "multiply";
enum operaterName(string _ : "/") = "divide";
enum operaterName(string _ : "%") = "modulus";
enum operaterName(string _ : "+") = "add";
enum operaterName(string _ : "-") = "subtract";
enum operaterName(string _ : "==") = "equal";
enum operaterName(string _ : "!=") = "not equal";
enum operaterName(string _ : "&&") = "and";
enum operaterName(string _ : "||") = "or";

Expression semanticImpl(string op)(ParserBinary!op that, Context context) if (["<=", ">=", ">", "<", "*", "/", "%", "+", "-", "==", "!=", "&&", "||"].canFind(op)) {
	auto left = semanticRuntime(that.left, context);
	auto right = semanticRuntime(that.right, context);
	return context.semanticDesugar!(operaterName!op)(that.position, [left, right]);
}

enum prefixOperaterName(string _ : "!") = "not";
enum prefixOperaterName(string _ : "-") = "negate";
enum prefixOperaterName(string _ : "*") = "derefence";

Expression semanticImpl(string op)(ParserPrefix!op that, Context context) if (["!", "-", "*"].canFind(op)) {
	auto value = semanticRuntime(that.value, context);
	return context.semanticDesugar!(prefixOperaterName!op)(that.position, value);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context) if (["+", "/"].canFind(op)) {
	error(op ~ " not supported", that.position);
	return null;
}

Expression semanticImpl(Parser.StringLit that, Context context) {
	return make!StringLit(make!TypeArray(make!StageRuntime, make!TypeChar(make!StageRuntime)), that.value);
}

Expression semanticImpl(Parser.ArrayLit that, Context context) {
	auto variable = context.freshTypeVariable(make!StageRuntime, that.position);
	context.predicateCheck(make!PredicateUnrestricted, variable, that.position);
	auto type = make!TypeArray(make!StageRuntime, variable);
	auto values = that.values.map!(a => semanticRuntime(a, context)).cache.array;
	foreach (value; values) {
		context.typeCheck(variable, value.type, that.position);
	}

	return make!ArrayLit(type, values);
}

Expression semanticImpl(Parser.ExternJs that, Context context) {
	error("Extern only allowed in external variable", that.position);
	assert(0);
}
