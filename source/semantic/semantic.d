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

import app : knownBindings, readSemanticModule, freshId, knownSymbols;
import Parser = parser.ast;
import semantic.astimpl;

import misc.position;
import misc.container;
import misc.misc;

Module createModule(Parser.Module parser, Module parent) {
	OwnerDictonary!(string, Parser.ModuleBinding) rawBindings;
	foreach (binding; parser.bindings) {
		check(!(binding.name in rawBindings), "Binding already exists", binding.position);
		rawBindings.insert(binding.name, binding);
	}
	auto rawBindingsFrozen = rawBindings.freeze;
	ModuleDefinition delegate(RecursionChecker) resolveBindingThunk(Parser.ModuleBinding binding) {
		ModuleDefinition thunk(RecursionChecker recursionCheck) {
			return resolveBinding(rawBindingsFrozen, binding, parent, recursionCheck);
		}

		return &thunk;
	}

	OwnerDictonary!(string, ModuleDefinition delegate(RecursionChecker)) aliases;
	ModuleDefinition delegate(RecursionChecker)[] orderedAliases;
	SymbolId delegate()[] exports;
	foreach (binding; parser.bindings) {
		auto value = resolveBindingThunk(binding);
		orderedAliases ~= value;
		aliases.insert(binding.name, value);
		if (binding.sort == Parser.BindingSort.symbol || binding.sort == Parser.BindingSort.generative) {
			exports ~= makeExport(value);
		}
	}
	auto ret = new Module;
	ret.orderedAliases = orderedAliases;
	ret.aliases = aliases.freeze;
	ret.exports = exports;
	return ret;
}

void validateModule(Module mod) {
	foreach (binding; mod.orderedAliases) {
		binding(RecursionChecker());
	}
}

SymbolId delegate() makeExport(ModuleDefinition delegate(RecursionChecker) thunk) {
	return { auto definition = thunk(RecursionChecker()); auto symbol = definition.matrix.castTo!SymbolReference; assert(symbol); return symbol.id; };
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

ModuleDefinition resolveBinding(Dictonary!(string, Parser.ModuleBinding) rawBindings, Parser.ModuleBinding binding, Module parent, RecursionChecker recursionCheck) {
	bool known = binding in knownBindings;
	bool disallowed = binding in recursionCheck.disallowed;
	// todo think about relation between recursive and intermediate
	bool recursive = binding in recursionCheck.recursive;
	bool intermediate = recursionCheck.frame && binding in recursionCheck.frame.typeChecker.bindingGroup;
	if (known) {
		assert(!recursive && !disallowed && !intermediate);
		return knownBindings[binding];
	} else if (disallowed) {
		assert(!known && !recursive && !intermediate);
		error("Illegal self reference", binding.position);
		assert(0);
	} else if (intermediate) {
		assert(!known && !disallowed);
		return ModuleDefinition(recursionCheck.frame.typeChecker.bindingGroup[binding]);
	} else if (recursive) {
		assert(!known && !disallowed);
		auto frame = recursionCheck.recursive[binding];
		frame.unifyTypeCheckers;
		auto checker = frame.typeChecker;
		assert(binding in checker.bindingGroup);
		return ModuleDefinition(checker.bindingGroup[binding]);
	} else {
		return semanticGlobal(rawBindings, binding, parent, recursionCheck);
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
	Dictonary!(Parser.ModuleBinding, Term) bindingGroup;
	Dictonary!(Parser.ModuleBinding, void delegate(Term, Term delegate(Term))) onBind;
	Dictonary!(TypeVariableId, TypeRequirement) freshTypeVariables;
	TypeAlgebra[] typeChecks;
	Dictonary!(RigidVariableId, RigidRequirement) freshRigidVariables;

	Dictonary!(StageVariableId, StageRequirement) freshStageVariables;
	StageAlgebra[] stageChecks;

	Dictonary!(SymbolId, Term delegate(Type delegate(Parser.ModuleBinding), Dictonary!(TypeVariableId, TypeRequirement))) forwardReplacements;

}

void moveTypeChecker(TypeChecker from, TypeChecker to) {
	if (from is to) {
		return;
	}
	to.bindingGroup = mergeMapsUnique(to.bindingGroup, from.bindingGroup);
	to.onBind = mergeMapsUnique(to.onBind, from.onBind);
	to.freshTypeVariables = mergeMapsUnique(to.freshTypeVariables, from.freshTypeVariables);
	to.typeChecks = to.typeChecks ~ from.typeChecks;
	to.freshStageVariables = mergeMapsUnique(to.freshStageVariables, from.freshStageVariables);
	to.freshRigidVariables = mergeMapsUnique(to.freshRigidVariables, from.freshRigidVariables);
	to.stageChecks = to.stageChecks ~ from.stageChecks;
	to.forwardReplacements = mergeMapsUnique(to.forwardReplacements, from.forwardReplacements);
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
	if (typeChecker.bindingGroup.length > 0) {

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

	}

	unifyAll(stageSystem);
	typeSystem.unsolved = typeSystem.unsolved.substitute(stageSystem.substitution);
	typeSystem.unsolvedRigid = typeSystem.unsolvedRigid.substitute(stageSystem.substitution);
	if (typeChecker.bindingGroup.length > 0) {
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
	}

	Type bindingType(Parser.ModuleBinding def) {
		return typeChecker.bindingGroup[def].type.substitute(typeSystem.substitution).substitute(typeSystem.substitutionRigid).substitute(stageSystem.substitution);
	}

	auto forward = typeChecker.forwardReplacements.mapValues!(a => a(&bindingType, typeSystem.unsolved));

	Term substituteAll(Term that) {
		return that.substitute(typeSystem.substitution).substitute(typeSystem.substitutionRigid).substitute(stageSystem.substitution).substitute(forward).reduceMacros;
	}

	foreach (binding, expression0; typeChecker.bindingGroup) {
		auto expression1 = substituteAll(expression0);
		knownBindings.insert(binding, ModuleDefinition(expression1, typeSystem.unsolved, stageSystem.unsolved));
		if (binding.sort == Parser.BindingSort.symbol) {
			check(expression1.type.freeVariables.length == 0, "Strong symbols cannot be generic", binding.position);
		}
		if (binding in typeChecker.onBind) {
			typeChecker.onBind[binding](expression1, &substituteAll);
		}
	}
}

struct RecursionChecker {
	TypeCheckerFrame* frame;
	Dictonary!(Parser.ModuleBinding, TypeCheckerFrame*) recursive;
	Set!(Parser.ModuleBinding) disallowed;
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

class DoBlock {
	Term delegate(Term)[] thunks;
}

class Context {
	// initialized when processing binding
	Dictonary!(string, Parser.ModuleBinding) rawGlobalBindings;
	RigidContextId rigidContext;
	RecursionChecker recursionCheck;
	Module parent; // nullable

	// mutable data
	TypeChecker typeChecker;
	Dictonary!(string, Expression[]) locals;
	Dictonary!(VariableId, Linearity) uses;
	DoBlock doBlock; // nullable

	this(Dictonary!(string, Parser.ModuleBinding) rawGlobalBindings, RecursionChecker recursionCheck, Module parent) {
		this.rawGlobalBindings = rawGlobalBindings;
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

	void removeTypeVariable(string name) {
		locals = locals.replaceCopy(name, locals[name][0 .. $ - 1]);
	}

	void bindTermVariable(Variable variable, Position position, bool duplicate) {
		locals = locals.insertIfMissing(variable.name, emptyArray!Expression);

		if (!duplicate && locals[variable.name].length != 0) {
			error("duplicate name", position);
		}
		locals = locals.replaceCopy(variable.name, locals[variable.name] ~ variable);
		uses = uses.insertCopy(variable.id, Linearity.unused);
	}

	void removeTermVariable(Variable variable, Context context, Position position) {
		if (uses[variable.id] != Linearity.linear) {
			this.predicateCheck(context.semanticDesugarPredicate!"unrestricted"(position), variable.type, position);
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
	if (name in context.rawGlobalBindings) {
		auto binding = context.rawGlobalBindings[name];
		auto resolved = resolveBinding(context.rawGlobalBindings, binding, context.parent, context.recursionCheck);
		return context.unpackModuleDefinition(resolved, position);
	} else if (context.parent) {
		if (name in context.parent.aliases) {
			auto binding = context.parent.aliases[name](context.recursionCheck);
			return context.unpackModuleDefinition(binding, position);
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

Predicate semanticDesugarPredicate(string name)(Context context, Position position) {
	auto builtin = searchGlobal(context, name, position);
	check(builtin, "Can't resolve builtin " ~ name, position);
	return assumeConstraint(builtin, position);
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

ModuleDefinition semanticGlobalOverload(Parser.ModuleBinding binding, Context context) {
	auto id = freshId!TypeVariableId;
	auto variable = make!TypeVariable(make!StageRuntime, id);
	context.bindTypeVariable(variable, binding.classTypeVariable, binding.position, false);
	auto base = semanticType(binding.classTypeScheme, context);
	context.removeTypeVariable(binding.classTypeVariable);
	auto match = semanticTypeMatch(binding.value, context);

	Type requirement(Type target) {
		return base.substitute(singletonMap(id, target));
	}

	match.validate(&requirement, context, binding.value.position);
	context.typeChecker.evaluateTypeChecks;

	// need to reduce macros of terms inside type instances

	auto pid = PredicateId(PredicateCustomId(binding.position.source.fileName, binding.position.section.start));

	assert(!(binding in knownBindings));
	knownBindings.insert(binding, ModuleDefinition(make!PredicateTypeMatch(pid, match, &requirement)));
	return knownBindings[binding];
}

ModuleDefinition semanticGlobalInline(Parser.ModuleBinding binding, Context context) {
	Term term = semanticTerm(binding.value, context);
	if (binding in knownBindings) {
		// throw away work
		return knownBindings[binding];
	}
	if (binding.explicitType) {
		Type makeRigid(Stage stage, Dictonary!(PredicateId, Predicate) predicates, string name) {
			return context.freshRigidTypeVariable(stage, predicates, name, binding.position);
		}

		auto scheme = semanticTypeScheme(binding.explicitType, context);
		auto wanted = scheme.instantiate(&makeRigid);
		context.typeCheck(term.type, wanted, binding.position);
	}

	assert(!(binding in context.typeChecker.bindingGroup));
	context.typeChecker.bindingGroup = context.typeChecker.bindingGroup.insertCopy(binding, term);

	assert(!context.recursionCheck.frame.referenced);
	context.typeChecker.evaluateTypeChecks;
	assert(binding in knownBindings);
	return knownBindings[binding];
}

ModuleDefinition semanticGlobalSymbol(Parser.ModuleBinding binding, Context context) {
	auto strong = binding.sort == Parser.BindingSort.symbol;
	auto argument = context.freshTypeVariable(make!StageRuntime, binding.position);
	auto result = context.freshTypeVariable(make!StageRuntime, binding.position);
	auto expectedType = make!TypeFunction(make!StageRuntime, result, argument);
	if (binding.explicitType) {
		Type makeRigid(Stage stage, Dictonary!(PredicateId, Predicate) predicates, string name) {
			return context.freshRigidTypeVariable(stage, predicates, name, binding.position);
		}

		auto scheme = semanticTypeScheme(binding.explicitType, context);
		auto wanted = scheme.instantiate(&makeRigid);
		context.typeCheck(expectedType, wanted, binding.position);
	}
	auto forward = make!SymbolForwardReference(expectedType, freshId!SymbolId);
	assert(!(binding in context.typeChecker.bindingGroup));
	context.typeChecker.bindingGroup = context.typeChecker.bindingGroup.insertCopy(binding, forward);

	auto internalType = make!TypeMacro(make!StageMacro(result.type, argument.type), result, argument);
	auto internal = semanticTerm(binding.value, context);
	context.typeCheck(internalType, internal.type, binding.position);

	Term makeReplacement(Type delegate(Parser.ModuleBinding) bindingType, Dictonary!(TypeVariableId, TypeRequirement) requirements) {
		auto type = bindingType(binding);
		return make!SymbolReference(type, binding.name, forward.id, type.dictonaryOf(requirements));
	}

	context.typeChecker.forwardReplacements = context.typeChecker.forwardReplacements.insertCopy(forward.id, &makeReplacement);

	void addGlobalValue(Term reference, Term delegate(Term) substitute) {
		auto symbol = reference.castTo!SymbolReference;
		assert(symbol);
		auto linkage = strong ? Linkage.strong : Linkage.weak;
		auto reduced = substitute(internal);
		knownSymbols.insert(forward.id, SymbolValue(reduced, linkage, binding.name, symbol.dictonaries.map!(a => tuple(a[0].castTo!TypeVariable, a[1])).array));
	}

	context.typeChecker.onBind = context.typeChecker.onBind.insertCopy(binding, &addGlobalValue);
	if (context.recursionCheck.frame.referenced) {
		return ModuleDefinition(context.recursionCheck.frame.typeChecker.bindingGroup[binding]);
	} else {
		context.typeChecker.evaluateTypeChecks;
		assert(binding in knownBindings);
		return knownBindings[binding];
	}
}

ModuleDefinition semanticGlobal(Dictonary!(string, Parser.ModuleBinding) parserGlobals, Parser.ModuleBinding binding, Module parent, RecursionChecker recursionCheck) {
	assert(!(binding in recursionCheck.recursive) && !(binding in recursionCheck.disallowed));

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
	if (binding.sort == Parser.BindingSort.overload) {
		auto disallowed = recursionCheck.disallowed.insertCopy(binding);
		auto recursive = recursionCheck.recursive;
		auto checker = RecursionChecker(&frame, recursive, disallowed);
		auto context = new Context(parserGlobals, checker, parent);
		return semanticGlobalOverload(binding, context);
	} else if (binding.sort == Parser.BindingSort.inline) {
		auto disallowed = recursionCheck.disallowed.insertCopy(binding);
		auto recursive = recursionCheck.recursive;
		auto checker = RecursionChecker(&frame, recursive, disallowed);
		auto context = new Context(parserGlobals, checker, parent);
		return semanticGlobalInline(binding, context);
	} else {
		// remove inlines from disallowed stack
		auto disallowed = emptySet!(Parser.ModuleBinding);
		auto recursive = recursionCheck.recursive.insertCopy(binding, &frame);
		auto checker = RecursionChecker(&frame, recursive, disallowed);
		auto context = new Context(parserGlobals, checker, parent);
		return semanticGlobalSymbol(binding, context);
	}
}

TypeVariableRigid freshRigidTypeVariable(Context context, Stage stage, Dictonary!(PredicateId, Predicate) predicates, string name, Position position) {
	auto id = freshId!RigidVariableId;
	auto var = make!TypeVariableRigid(stage, id, name, context.rigidContext);
	context.typeChecker.freshRigidVariables = context.typeChecker.freshRigidVariables.insertCopy(id, RigidRequirement(position, stage, predicates));
	return var;
}

Expression semanticForall(Parser.ForallBinding[] bindings, Parser.Expression value, Position position, Context context) {
	if (bindings.length == 0) {
		return semanticMain(value, context);
	} else {
		auto binding = bindings[0];
		auto predicates = binding.predicates
			.map!(a => semanticConstraint(a, context))
			.cache
			.map!(a => item(a.id, a))
			.rangeToMap;
		auto stage = context.freshStageVariable(position);
		auto id = freshId!TypeVariableId;
		context.bindTypeVariable(make!TypeVariable(stage, id), binding.name, position, false);
		auto enclosed = semanticForall(bindings[1 .. $], value, position, context).assumeTypeScheme(position);
		context.removeTypeVariable(binding.name);
		return make!TypeSchemeForall(id, stage, predicates, binding.name, enclosed);
	}
}

void matchValidate(TypeMatchEqual, Type delegate(Type) requirement, Context context, Position position) {
	auto variable = context.freshRigidTypeVariable(make!StageRuntime, emptyMap!(PredicateId, Predicate), "builtin variable", position);
	context.typeCheck(requirement(variable), requireEqual(variable), position);
}

void matchValidate(TypeMatchNumber, Type delegate(Type) requirement, Context context, Position position) {
	auto variable = context.freshRigidTypeVariable(make!StageRuntime, emptyMap!(PredicateId, Predicate), "builtin variable", position);
	context.typeCheck(requirement(variable), requireNumber(variable), position);
}

void matchValidate(TypeMatchUnrestricted, Type delegate(Type) requirement, Context context, Position position) {
	assert(0);
}

void matchValidate(TypeMatchCustom custom, Type delegate(Type) requirement, Context context, Position position) {
	OwnerDictonary!(RigidVariableId, Tuple!()) remaining;
	Type makeRigid(Stage stage, Dictonary!(PredicateId, Predicate) predicates, string name) {
		auto variable = context.freshRigidTypeVariable(stage, predicates, name, position);
		remaining.insert(variable.id, tuple());
		return variable;
	}

	Type substituted = custom.pattern.instantiate(&makeRigid);

	auto error = "instances must be a type constructor applied to unique type variables or types without type variables";

	check(!substituted.castTo!TypeVariableRigid, error, position);
	foreach (inner; substituted.internal) {
		if (auto variable = inner.castTo!TypeVariableRigid) {
			check(variable.id in remaining, error, position);
			remaining.remove(variable.id);
		} else {
			check(inner.freeRigidVariables.length == 0, error, position);
		}
	}

	Type target = requirement(substituted);

	context.typeCheck(target, custom.match.type, position);
}

void matchValidate(TypeMatchOr or, Type delegate(Type) requirement, Context context, Position position) {
	or.left.validate(requirement, context, position);
	or.right.validate(requirement, context, position);
}

Expression semanticImpl(Parser.Forall that, Context context) {
	return semanticForall(that.bindings, that.value, that.position, context);
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
	return predicateEqual;
}

Expression builtinImpl(string name : "number")() {
	return predicateNumber;
}

Expression builtinImpl(string name : "unrestricted")() {
	return predicateUnrestricted;
}

Expression builtinImpl(string name : "match equal")() {
	return make!TypeMatchEqual;
}

Expression builtinImpl(string name : "match number")() {
	return make!TypeMatchNumber;
}

Expression builtinImpl(string name : "match unrestricted")() {
	return make!TypeMatchUnrestricted;
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

enum builtins = AliasSeq!("true", "false", "boolean", "character", "equal", "number", "unrestricted", "match equal", "match number", "match unrestricted", "world", "integer", "integer8", "integer16", "integer32", "integer64", "natural", "natural8", "natural16", "natural32", "natural64");

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

TypeScheme assumeTypeScheme(Expression value, Position position, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!TypeScheme, "Expected type scheme", position, file, line);
	return value.castTo!TypeScheme;
}

TypeMatch assumeTypeMatch(Expression value, Position position, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!TypeMatch, "Expected type match", position, file, line);
	return value.castTo!TypeMatch;
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

TypeScheme semanticTypeScheme(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeTypeScheme(semanticMain(that, context), that.position, file, line);
}

Type semanticTypeRuntime(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeTypeRuntime(semanticMain(that, context), context, that.position, file, line);
}

TypeMatch semanticTypeMatch(Parser.Expression that, Context context, string file = __FILE__, int line = __LINE__) {
	return assumeTypeMatch(semanticMain(that, context), that.position, file, line);
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
	auto variable = make!Variable(argument.type, "", freshId!VariableId);

	auto definition = make!VariableDefinition(value.type, argument, variable, value);
	return make!MacroFunctionLiteral(type, Argument(variable.id, ""), definition);
}

Expression semanticImpl(Parser.MacroFunctionLiteral that, Context context) {
	auto freshStage = context.freshStageVariable(that.position);
	auto freshType = context.freshTypeVariable(freshStage, that.position);

	auto variable = make!Variable(freshType, that.argument, freshId!VariableId);
	context.bindTermVariable(variable, that.position, that.shadow);

	auto text = semanticTerm(that.text, context);
	auto type = make!TypeMacro(make!StageMacro(text.type.type, variable.type.type), text.type, variable.type);
	return make!MacroFunctionLiteral(type, Argument(variable.id, variable.name), text);
}

Term callRuntime(Context context, Position position) {
	auto a = context.freshTypeVariable(make!StageRuntime, position);
	auto b = context.freshTypeVariable(make!StageRuntime, position);
	auto wrapper = make!Variable(make!TypeFunction(make!StageRuntime, a, b), "f", freshId!VariableId);
	auto argument = make!Variable(a, "a", freshId!VariableId);
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

Term foldDoBlock(Term effectless, Term delegate(Term)[] doBlock, Position position, Context context) {
	auto effect = context.semanticDesugar!"pure"(position, effectless);
	foreach (thunk; doBlock.retro) {
		effect = thunk(effect);
	}
	return effect;
}

Expression semanticImpl(Parser.Do that, Context context) {
	auto previous = context.doBlock;
	scope (exit) {
		context.doBlock = previous;
	}
	context.doBlock = new DoBlock;
	auto effectless = that.value.semanticTerm(context);

	return foldDoBlock(effectless, context.doBlock.thunks, that.position, context);
}

Term delegate(Term) makeTryClosure(Term effect, Variable variable, Position position, Context context) {
	Term closure(Term dependent) {
		auto type = make!TypeMacro(make!StageMacro(dependent.type.type, variable.type.type), dependent.type, variable.type);
		auto continuation = make!MacroFunctionLiteral(type, Argument(variable.id, variable.name), dependent);
		return context.semanticDesugar!"bind"(position, [effect, continuation]);
	}

	return &closure;
}

Term semanticTry(Term effect, Position position, Context context) {
	auto id = freshId!VariableId;
	auto stage = context.freshStageVariable(position);
	auto type = context.freshTypeVariable(stage, position);

	auto variable = make!Variable(type, "", id);
	assert(context.doBlock);
	context.doBlock.thunks ~= makeTryClosure(effect, variable, position, context);
	return variable;
}

Expression semanticImpl(Parser.Try that, Context context) {
	check(context.doBlock, "Expected do block for try", that.position);
	auto effect = semanticTerm(that.value, context);
	return semanticTry(effect, that.position, context);
}

Term semanticImpl(Parser.Run that, Context context) {
	check(context.doBlock, "run without do block", that.position);

	auto value = semanticTry(semanticTerm(that.value, context), that.position, context);
	auto variable = make!TuplePattern(typeStructFrom(), emptyArray!Pattern);
	context.typeCheck(variable.type, value.type, that.position);
	context.doBlock.thunks ~= dependent => make!VariableDefinition(dependent.type, variable, value, dependent);

	return semanticTerm(that.last, context);
}

Term semanticImpl(Parser.VariableDefinition that, Context context) {
	auto value = semanticTerm(that.value, context);
	auto variable = semanticPattern(that.variable, context);
	context.typeCheck(variable.type, value.type, that.position);
	addBindings(variable, that.variable.position, context);

	if (context.doBlock) {
		context.doBlock.thunks ~= dependent => make!VariableDefinition(dependent.type, variable, value, dependent);
	}

	auto last = semanticTerm(that.last, context);
	removeBindings(variable, that.variable.position, context);
	if (context.doBlock) {
		return last;
	} else {
		return make!VariableDefinition(last.type, variable, value, last);
	}
}

void addBindings(Pattern variable, Position position, Context context) {
	foreach (binding; variable.orderedBindings) {
		context.bindTermVariable(binding[0], position, binding[1]);
	}
}

void removeBindings(Pattern variable, Position position, Context context) {
	foreach (binding; variable.orderedBindings) {
		context.removeTermVariable(binding[0], context, position);
	}
}

Pattern semanticImpl(Parser.NamedArgument that, Context context) {
	auto type = context.freshTypeVariable(make!StageRuntime, that.position);
	return make!NamedPattern(type, freshId!VariableId, that.name, that.shadow);
}

Pattern semanticImpl(Parser.TupleArgument that, Context context) {
	auto matches = that.matches.map!(a => semanticPattern(a, context)).cache.array;
	auto type = make!TypeStruct(make!StageRuntime, matches.map!(a => a.type).array);
	return make!TuplePattern(type, matches);
}

Expression semanticImpl(Parser.ConstraintTuple that, Context context) {
	auto type = semanticType(that.type, context);
	return predicateTuple(that.index, type);
}

Expression semanticImpl(Parser.Variable that, Context context) {
	auto variable = context.search(that.name, that.position);
	check(!(variable is null), "Undefined variable", that.position);
	return variable;
}

Expression semanticImpl(Parser.Import that, Context context) {
	return make!Import(readSemanticModule(that.value()));
}

Expression semanticImpl(Parser.UseSymbol that, Context context) {
	auto value = semanticMain(that.value, context);
	auto Import = value.castTo!Import;
	check(Import, "scope resolution expect an import", that.position);
	check(that.index in Import.mod.aliases, "Undefined variable", that.position);
	return context.unpackModuleDefinition(Import.mod.aliases[that.index](context.recursionCheck), that.position);
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
	context.predicateCheck(context.semanticDesugarPredicate!"number"(that.position), variable, that.position);
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
	auto cond = semanticTerm(that.cond, context);
	auto condUses = context.uses;
	context.uses = context.uses.mapValues!(_ => Linearity.unused);
	Term delegate(Term)[] condDo;
	if (context.doBlock) {
		condDo = context.doBlock.thunks;
		context.doBlock.thunks = [];
	}

	auto yes = semanticTerm(that.yes, context);
	auto yesUses = context.uses;
	context.uses = context.uses.mapValues!(_ => Linearity.unused);
	Term delegate(Term)[] yesDo;
	if (context.doBlock) {
		yesDo = context.doBlock.thunks;
		context.doBlock.thunks = [];
	}

	auto no = semanticTerm(that.no, context);
	auto noUses = context.uses;
	context.uses = context.uses.mapValues!(_ => Linearity.unused);
	Term delegate(Term)[] noDo;
	if (context.doBlock) {
		noDo = context.doBlock.thunks;
		context.doBlock.thunks = [];
	}

	context.typeCheck(cond.type, make!TypeBool(make!StageRuntime), that.cond.position);
	context.typeCheck(yes.type, no.type, that.position);

	context.uses = mergeMaps!both(condUses, mergeMaps!branch(yesUses, noUses));
	if (context.doBlock) {
		context.doBlock.thunks = condDo;
		auto yesEffect = foldDoBlock(yes, yesDo, that.yes.position, context);
		auto noEffect = foldDoBlock(no, noDo, that.no.position, context);
		auto effect = context.semanticDesugar!"choose"(that.position, [cond, yesEffect, noEffect]);
		return semanticTry(effect, that.position, context);
	} else {
		return make!If(yes.type, cond, yes, no);
	}
}

Expression semanticImpl(Parser.Infer that, Context context) {
	auto argumentType = semanticType(that.type, context);
	auto value = semanticTerm(that.value, context);
	context.typeCheck(argumentType, value.type, that.position);
	return value;
}

Expression semanticImpl(Parser.Index that, Context context) {
	auto array = semanticTerm(that.array, context);
	auto index = semanticTerm(that.index, context);
	return context.semanticDesugar!"index"(that.position, [array, index]);
}

Expression semanticImpl(Parser.IndexAddress that, Context context) {
	auto array = semanticTerm(that.array, context);
	auto index = semanticTerm(that.index, context);
	return context.semanticDesugar!"index address"(that.position, [array, index]);
}

Expression semanticImpl(Parser.Binary!"<-" that, Context context) {
	auto pointer = semanticTerm(that.left, context);
	auto target = semanticTerm(that.right, context);
	return context.semanticDesugar!"assign"(that.position, [pointer, target]);
}

Expression semanticImpl(Parser.Binary!"|||" that, Context context) {
	auto left = semanticTypeMatch(that.left, context);
	auto right = semanticTypeMatch(that.right, context);
	return make!TypeMatchOr(left, right);
}

Expression semanticImpl(Parser.TupleIndex that, Context context) {
	auto tuple = semanticRuntime(that.tuple, context);
	auto index = that.index;

	auto returnType = context.freshTypeVariable(make!StageRuntime, that.position);
	auto argumentType = context.freshTypeVariable(make!StageRuntime, that.position);
	auto predicate = predicateTuple(that.index, returnType);
	auto getter = context.semanticDesugar!"fst"(that.position, semanticRequire(predicate, argumentType, that.position, context));
	return semanticCall(getter, tuple, that.position, context);
}

Expression semanticImpl(Parser.TupleIndexAddress that, Context context) {
	auto tuple = semanticRuntime(that.tuple, context);
	auto index = that.index;

	auto returnType = context.freshTypeVariable(make!StageRuntime, that.position);
	auto argumentType = context.freshTypeVariable(make!StageRuntime, that.position);
	auto predicate = predicateTuple(that.index, returnType);
	auto getter = context.semanticDesugar!"snd"(that.position, semanticRequire(predicate, argumentType, that.position, context));
	return semanticCall(getter, tuple, that.position, context);
}

Expression semanticImpl(Parser.Slice that, Context context) {
	auto array = semanticTerm(that.array, context);
	auto left = semanticTerm(that.left, context);
	auto right = semanticTerm(that.right, context);
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
	auto left = semanticTerm(that.left, context);
	auto right = semanticTerm(that.right, context);
	return context.semanticDesugar!(operaterName!op)(that.position, [left, right]);
}

enum prefixOperaterName(string _ : "!") = "not";
enum prefixOperaterName(string _ : "-") = "negate";
enum prefixOperaterName(string _ : "*") = "derefence";

Expression semanticImpl(string op)(ParserPrefix!op that, Context context) if (["!", "-", "*"].canFind(op)) {
	auto value = semanticTerm(that.value, context);
	return context.semanticDesugar!(prefixOperaterName!op)(that.position, value);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context) if (["+", "/"].canFind(op)) {
	error(op ~ " not supported", that.position);
	return null;
}

Expression semanticImpl(Parser.StringLit that, Context context) {
	return context.semanticDesugar!"effect"(that.position, make!StringLit(make!TypeArray(make!StageRuntime, make!TypeChar(make!StageRuntime)), that.value));
}

Expression semanticImpl(Parser.ArrayLit that, Context context) {
	auto variable = context.freshTypeVariable(make!StageRuntime, that.position);
	context.predicateCheck(context.semanticDesugarPredicate!"unrestricted"(that.position), variable, that.position);
	auto type = make!TypeArray(make!StageRuntime, variable);
	auto values = that.values.map!(a => semanticTerm(a, context)).cache.array;
	foreach (value; values) {
		context.typeCheck(variable, value.type, that.position);
	}

	return context.semanticDesugar!"effect"(that.position, make!ArrayLit(type, values));
}

Term semanticRequire(Predicate predicate, Type variable, Position position, Context context) {
	context.predicateCheck(predicate, variable, position);
	auto type = predicate.require(variable);
	return make!Requirement(type, predicate, variable);
}

Expression semanticImpl(Parser.Requirement that, Context context) {
	auto predicate = that.value.semanticConstraint(context);
	auto variable = context.freshTypeVariable(make!StageRuntime, that.position);
	return semanticRequire(predicate, variable, that.position, context);
}

Expression semanticImpl(Parser.Instance that, Context context) {
	auto pattern = semanticTypeScheme(that.type, context);
	auto match = semanticTerm(that.term, context);
	return make!TypeMatchCustom(pattern, match);
}

// todo readd predicates to extern
Expression semanticImpl(Parser.ExternJs that, Context context) {
	auto scheme = semanticTypeScheme(that.scheme, context);
	Dictonary!(TypeVariableId, TypeRequirement) requirements;
	Type makeFresh(Stage stage, Dictonary!(PredicateId, Predicate) predicates, string name) {
		auto fresh = context.freshTypeVariable(stage, that.position);
		foreach (id, predicate; predicates) {
			context.predicateCheck(predicate, fresh, that.position);
		}
		requirements = requirements.insertCopy(fresh.id, TypeRequirement(that.position, stage, predicates));
		return fresh;
	}

	auto type = scheme.instantiate(&makeFresh);
	return make!ExternJs(type, that.name, dictonaryOf(type, requirements));
}
