//the heart of the compiler
module unify;

import std.array;
import std.algorithm;
import std.range;
import std.conv;
import std.typecons;

import misc.misc;
import misc.container;
import misc.position;

template Unifier(alias make, alias decomposeEquation, alias decomposeCheck, VariableId, Variable, RigidVariableId, RigidContextId, RigidVariable, Term, PredicateId, Predicate, Algebra, Equation, Call, System, Parent, ParentEquation) {
	enum rigid = !is(RigidVariable == void);
	enum typed = !is(Parent == void);

	Requirement mapPredicates(alias f, Requirement)(Requirement requirement) {
		requirement.predicates = f(requirement.predicates);
		return requirement;
	}

	Algebra[] reapplyPredicates(Dictonary!(PredicateId, Predicate) predicates, Term term, Position position) {
		return predicates.byValue.map!(predicate => make!Call(predicate, term, position).convert!Algebra).array;
	}

	Dictonary!(Id, Term) composeSubsitution(Var, Id)(Dictonary!(Id, Term) sigma, Dictonary!(Id, Term) theta) {
		auto sigma1 = sigma.mapValues!(a => a.substitute(theta));
		auto theta1 = theta.removeRangeIfExists(sigma.byKey);
		auto sigma2 = sigma1.range.filter!(a => a.value.castTo!Var ? a.key != a.value.castTo!Var.id : true).rangeToMap;
		return mergeMapsUnique(sigma2, theta1);
	}

	void applySubstitution(Variable variable, Term term, Position position, System system) {
		static if (typed) {
			system.parent.algebra ~= make!ParentEquation(variable.type, term.type, position);
		}
		auto substitution = singletonMap(variable.id, term);
		system.algebra = system.algebra.map!(a => a.substitute(substitution)).array;
		system.substitution = composeSubsitution!Variable(system.substitution, substitution);
		system.algebra ~= system.unsolved[variable.id].predicates.reapplyPredicates(term, position);
		system.unsolved = system.unsolved.removeCopy(variable.id);
		system.unsolved = system.unsolved.mapValues!(requirement => requirement.mapPredicates!(predicates => predicates.mapValues!(predicate => predicate.substitute(substitution))));
	}

	static if (rigid) {
		void applySubstitution(RigidVariable variable, RigidVariable term, Position position, System system) {
			static if (typed) {
				system.parent.algebra ~= make!ParentEquation(variable.type, term.type, position);
			}
			auto substitution = singletonMap(variable.id, term.convert!Term);
			system.algebra = system.algebra.map!(a => a.substitute(substitution)).array;
			system.substitution = system.substitution.mapValues!(a => a.substitute(substitution));
			system.unsolved = system.unsolved.mapValues!(requirement => requirement.mapPredicates!(predicates => predicates.mapValues!(predicate => predicate.substitute(substitution))));

			system.substitutionRigid = composeSubsitution!RigidVariable(system.substitutionRigid, substitution);
			system.unsolvedRigid = system.unsolvedRigid.removeCopy(variable.id);
			system.unsolvedRigid = system.unsolvedRigid.mapValues!(requirement => requirement.mapPredicates!(predicates => predicates.mapValues!(predicate => predicate.substitute(substitution))));
		}
	}

	void unifyImpl(Variable left, Variable right, Position position, System system) {
		if (left.id != right.id) {
			applySubstitution(left, right, position, system);
		}
	}

	void unifyImpl(T)(Variable variable, T term, Position position, System system) if (!is(T : Variable)) {
		if (variable.id in term.freeVariables) {
			error(variable.to!string ~ " occurs in " ~ term.to!string, position);
		} else {
			applySubstitution(variable, term, position, system);
		}
	}

	void unifyImpl(T)(T term, Variable variable, Position position, System system) if (!is(T : Variable)) {
		unifyImpl(variable, term, position, system);
	}

	void unifyImpl(T)(T left, T right, Position position, System system) if (!is(T : Variable) && !is(T : RigidVariable)) {
		system.algebra ~= decomposeEquation(left, right, position);
	}

	void unifyImpl(T1, T2)(T1 left, T2 right, Position position, System system) if (!is(T1 == T2) && !is(T1 : Variable) && !is(T2 : Variable)) {
		static assert(!is(T1 : T2));
		static assert(!is(T2 : T1));
		error("Can't match " ~ left.to!string ~ " to " ~ right.to!string, position);
	}

	static if (rigid) {
		void unifyImpl(RigidVariable left, RigidVariable right, Position position, System system) {
			if (left.id == right.id) {
				return;
			}
			auto leftPredicates = system.unsolvedRigid[left.id].predicates;
			auto rightPredicates = system.unsolvedRigid[right.id].predicates;
			if (left.context != right.context && isSubSet(leftPredicates.keys, rightPredicates.keys) && isSubSet(rightPredicates.keys, leftPredicates.keys)) {
				auto combined = mergePredicates(leftPredicates, rightPredicates, position, system);
				assert(isSubSet(combined.keys, leftPredicates.keys) && isSubSet(leftPredicates.keys, combined.keys));
				assert(isSubSet(combined.keys, rightPredicates.keys) && isSubSet(rightPredicates.keys, combined.keys));
				applySubstitution(left, right, position, system);
			} else {
				error("Can't match " ~ left.to!string ~ " to " ~ right.to!string, position);
			}
		}
	}

	void checkImpl(Predicate predicate, Variable variable, Position position, System system) {
		assert(variable.id in system.unsolved);
		if (variable.id in predicate.freeVariables) {
			error(variable.to!string ~ " occurs in " ~ predicate.to!string, position);
		}
		auto requirement = system.unsolved[variable.id];
		auto predicates = requirement.predicates;
		auto fresh = singletonMap(predicate.id, predicate.convert!Predicate);
		requirement.predicates = mergePredicates(predicates, fresh, position, system);
		system.unsolved = system.unsolved.replaceCopy(variable.id, requirement);
	}

	Dictonary!(PredicateId, Predicate) mergePredicates(Dictonary!(PredicateId, Predicate) left, Dictonary!(PredicateId, Predicate) right, Position position, System system) {
		auto intersection = intersectMaps(left, right);
		foreach (id, predicatePair; intersection) {
			system.algebra ~= predicatePair[0].decompose(predicatePair[1], position);
		}
		return mergeMapsLeft(left, right);
	}

	static if (rigid) {
		void checkImpl(C)(C predicate, RigidVariable variable, Position position, System system) {
			auto predicates = system.unsolvedRigid[variable.id].predicates;
			if (predicate.id in predicates) {
				system.algebra ~= predicate.decompose(predicates[predicate.id], position);
			} else {
				error("Can't match constraint " ~ predicate.toString ~ " to " ~ variable.toString, position);
			}
		}
	}

	void checkImpl(C, T)(C predicate, T term, Position position, System system) if (!is(T : Variable) && !is(T : RigidVariable)) {
		system.algebra ~= decomposeCheck(predicate, term, position);
	}

	void unifyAll(System system) {
		while (!system.algebra.empty) {
			auto head = system.algebra.back;
			system.algebra.popBack;
			head.reduce(system);
		}
	}

}
