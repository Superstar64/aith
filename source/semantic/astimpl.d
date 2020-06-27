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
module semantic.astimpl;

import std.meta;
import std.typecons;
import std.conv;
import std.algorithm;
import std.range;

public import semantic.ast;
import unify;
import Parser = parser.ast;

import misc.nonstrict;
import misc.getters;
import misc.position;
import misc.container;
import misc.misc;

template make(T) {
	T make(A...)(A args) {
		return new Impl!T(args);
	}
}

enum isImpl(_ : Impl!T, T) = true;
enum isImpl(_) = false;

// todo remove global state
PredicateId predicateId(_ : PredicateNumber)(PredicateNumber predicate) {
	static __gshared value = new PredicateId();
	return value;
}

PredicateId predicateId(_ : PredicateEqual)(PredicateEqual predicate) {
	static __gshared value = new PredicateId();
	return value;
}

PredicateId predicateId(_ : PredicateUnrestricted)(PredicateUnrestricted predicate) {
	static __gshared value = new PredicateId();
	return value;
}

PredicateId predicateId(_ : PredicateTuple)(PredicateTuple predicate) {
	static __gshared PredicateId[int] values;
	if (!(predicate.index in values)) {
		values[predicate.index] = new PredicateId;
	}
	return values[predicate.index];
}

auto renameBindings(Tuple!(Variable, bool)[] bindings) {
	return bindings.map!(a => item(a[0].id, new VariableId)).rangeToMap;
}

class Impl(T : Import) : Getters!T {
	this(A...)(A arguments) {
		super(arguments);
	}
}

class Impl(T : Term) : Getters!T if (!isImpl!T) {
	this(A...)(A arguments) {
		super(arguments);
	}

	import Js = jsast;
	import codegen.codegen : Extra, generateJsImpl;

override:

	Term substitute(Dictonary!(TypeVariableId, Type) moves) {
		return this.destructure!(mapTermAll!(a => a.substitute(moves), a => a.substitute(moves), a => a.substitute(moves), a => a.substitute(moves), T, make!T));
	}

	Term substitute(Dictonary!(RigidVariableId, Type) moves) {
		return this.destructure!(mapTermAll!(a => a.substitute(moves), a => a.substitute(moves), a => a.substitute(moves), a => a.substitute(moves), T, make!T));
	}

	Term substitute(Dictonary!(StageVariableId, Stage) moves) {
		return this.destructure!(mapTermAll!(a => a.substitute(moves), a => a.substitute(moves), a => a.substitute(moves), a => a.substitute(moves), T, make!T));
	}

	static if (is(T : Variable)) {
		Term substitute(Dictonary!(VariableId, Term) moves) {
			if (id in moves) {
				return moves[id];
			} else {
				return this;
			}
		}

		Term substitute(Dictonary!(VariableId, VariableId) moves) {
			if (id in moves) {
				return make!Variable(type, name, moves[id]);
			} else {
				return this;
			}
		}
	} else static if (is(T : VariableDefinition)) {
		Term substitute(Dictonary!(VariableId, Term) moves) {
			auto value = value.substitute(moves);
			auto bindings = variable.orderedBindings.map!(a => a[0].id);
			auto last = this.last.substitute(moves.removeRangeIfExists(bindings));
			return make!VariableDefinition(type, variable, value, last);
		}

		Term substitute(Dictonary!(VariableId, VariableId) moves) {
			auto value = value.substitute(moves);
			auto bindings = variable.orderedBindings.map!(a => a[0].id);
			auto last = this.last.substitute(moves.removeRangeIfExists(bindings));
			return make!VariableDefinition(type, variable, value, last);
		}
	} else static if (is(T : MacroFunctionLiteral)) {
		Term substitute(Dictonary!(VariableId, Term) moves) {
			auto text = this.text.substitute(moves.removeIfExists(argument.id));
			return make!MacroFunctionLiteral(type, argument, text);
		}

		Term substitute(Dictonary!(VariableId, VariableId) moves) {
			auto text = this.text.substitute(moves.removeIfExists(argument.id));
			return make!MacroFunctionLiteral(type, argument, text);
		}
	} else {
		Term substitute(Dictonary!(VariableId, Term) moves) {
			return this.destructure!(mapTerm!(a => a.substitute(moves), T, make!T));
		}

		Term substitute(Dictonary!(VariableId, VariableId) moves) {
			return this.destructure!(mapTerm!(a => a.substitute(moves), T, make!T));
		}
	}
	static if (is(T : SymbolForwardReference)) {
		Term substitute(Lazy!(Dictonary!(SymbolId, Term)) moves) {
			assert(id in moves.get);
			return moves.get[id];
		}
	} else {
		Term substitute(Lazy!(Dictonary!(SymbolId, Term)) moves) {
			return this.destructure!(mapTerm!(a => a.substitute(moves), T, make!T));
		}
	}

	static if (is(T : VariableDefinition)) {
		Term alphaConvert() {
			auto bindings = variable.orderedBindings.renameBindings;
			auto variable = variable.substitute(bindings);
			auto value = value.alphaConvert;
			auto last = last.substitute(bindings).alphaConvert;
			return make!VariableDefinition(type, variable, value, last);
		}
	} else static if (is(T : MacroFunctionLiteral)) {
		Term alphaConvert() {
			auto bindings = singletonMap(argument.id, new VariableId);
			auto argument = Argument(bindings[argument.id], argument.name);
			auto text = text.substitute(bindings).alphaConvert;
			return make!MacroFunctionLiteral(type, argument, text);
		}
	} else {
		Term alphaConvert() {
			return this.destructure!(mapTerm!(a => a.alphaConvert, T, make!T));
		}
	}
	static if (is(T : MacroCall)) {
		Term reduceMacros() {
			auto calle = calle.reduceMacros;
			auto argument = argument.reduceMacros;
			if (auto lambda = calle.castTo!MacroFunctionLiteral) {
				return lambda.text.alphaConvert.substitute(singletonMap(lambda.argument.id, argument));
			} else {
				return make!MacroCall(type, calle, argument);
			}

		}
	} else static if (is(T : VariableDefinition)) {
		Term reduceMacros() {
			auto last = last.reduceMacros;
			if (auto lambda = last.castTo!MacroFunctionLiteral) {
				auto inner = make!VariableDefinition(lambda.text.type, variable, value, lambda.text);
				auto outer = make!MacroFunctionLiteral(lambda.type, lambda.argument, inner);
				return outer.reduceMacros;
			} else {
				return make!VariableDefinition(type, variable, value.reduceMacros, last);
			}
		}
	} else {
		Term reduceMacros() {
			return this.destructure!(mapTerm!(a => a.reduceMacros, T, make!T));
		}
	}

	Js.JsExpr generateJs(Js.JsScope depend, Extra extra) {
		return generateJsImpl(this, depend, extra);
	}
}

class Impl(T : Pattern) : Getters!T if (!isImpl!T) {
	this(A...)(A arguments) {
		super(arguments);
	}

	import Js = jsast;
	import codegen.codegen : Extra, generatePatternMatchImpl;
	import semantic.semantic;

override:

	Pattern substitute(Dictonary!(TypeVariableId, Type) moves) {
		return this.destructure!(mapPatternAll!(a => a.substitute(moves), a => a.substitute(moves), T, make!T));
	}

	Pattern substitute(Dictonary!(RigidVariableId, Type) moves) {
		return this.destructure!(mapPatternAll!(a => a.substitute(moves), a => a.substitute(moves), T, make!T));
	}

	Pattern substitute(Dictonary!(StageVariableId, Stage) moves) {
		return this.destructure!(mapPatternAll!(a => a.substitute(moves), a => a.substitute(moves), T, make!T));
	}

	static if (is(T : NamedPattern)) {
		Pattern substitute(Dictonary!(VariableId, VariableId) moves) {
			if (id in moves) {
				return make!NamedPattern(type, moves[id], name, shadow);
			} else {
				return this;
			}
		}
	} else {
		Pattern substitute(Dictonary!(VariableId, VariableId) moves) {
			return this.destructure!(mapPattern!(a => a.substitute(moves), T, make!T));
		}
	}

	Js.JsPattern generatePatternMatch(Extra extra) {
		return generatePatternMatchImpl(this, extra);
	}

	Tuple!(Variable, bool)[] orderedBindings() {
		return orderedBindingsImpl(this);
	}
}

class Impl(T : Type) : Getters!T if (!isImpl!T) {
	this(A...)(A arguments) {
		super(arguments);
	}

override:

	string toStringPrecedence(TypePrecedence precedence) {
		return toStringImpl(this, precedence);
	}

	void unify(Type right, Position position, TypeSystem system) {
		return right.unifyDispatch(this, position, system);
	}

	void unifyDispatch(TypeVariable left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeVariableRigid left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeBool left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeChar left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeInt left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeStruct left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeArray left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeFunction left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeMacro left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypePointer left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeOwnPointer left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeOwnArray left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyDispatch(TypeWorld left, Position position, TypeSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void checkDispatch(PredicateEqual left, Position position, TypeSystem system) {
		return checkImpl(left, this.convert!T, position, system);
	}

	void checkDispatch(PredicateNumber left, Position position, TypeSystem system) {
		return checkImpl(left, this.convert!T, position, system);
	}

	void checkDispatch(PredicateTuple left, Position position, TypeSystem system) {
		return checkImpl(left, this.convert!T, position, system);
	}

	void checkDispatch(PredicateUnrestricted left, Position position, TypeSystem system) {
		return checkImpl(left, this.convert!T, position, system);
	}

	static if (is(T : TypeVariable)) {
		Type substitute(Dictonary!(TypeVariableId, Type) moves) {
			if (id in moves) {
				return moves[id];
			} else {
				return this;
			}
		}

		Type substitute(Dictonary!(RigidVariableId, Type) moves) {
			return this;
		}

		Set!TypeVariableId freeVariables() {
			return id.only.rangeToSet;
		}

		TypeVariableId[] freeVariablesOrdered() {
			return [id];
		}

	} else static if (is(T : TypeVariableRigid)) {
		Type substitute(Dictonary!(TypeVariableId, Type) moves) {
			return this;
		}

		Type substitute(Dictonary!(RigidVariableId, Type) moves) {
			if (id in moves) {
				return moves[id];
			} else {
				return this;
			}
		}

		Set!TypeVariableId freeVariables() {
			return emptySet!TypeVariableId;
		}

		TypeVariableId[] freeVariablesOrdered() {
			assert(0);
		}
	} else {
		Type substitute(Dictonary!(TypeVariableId, Type) moves) {
			return this.destructure!(mapType!(a => a.substitute(moves), T, make!T));
		}

		Type substitute(Dictonary!(RigidVariableId, Type) moves) {
			return this.destructure!(mapType!(a => a.substitute(moves), T, make!T));
		}

		Set!TypeVariableId freeVariables() {
			alias folder = foldType!(Set!TypeVariableId, emptySet!TypeVariableId, mergeSets, T);
			return this.destructure!(mapType!(a => a.freeVariables, T, folder));
		}

		TypeVariableId[] freeVariablesOrdered() {
			alias folder = foldType!(TypeVariableId[], cast(TypeVariableId[])[], (a, b) => a ~ b, T);
			return this.destructure!(mapType!(a => a.freeVariablesOrdered, T, folder));
		}
	}

	Type substitute(Dictonary!(StageVariableId, Stage) moves) {
		return this.destructure!(mapTypeAll!(a => a.substitute(moves), a => a.substitute(moves), T, make!T));
	}

	import Js = jsast;
	import codegen.codegen : Extra, infoImpl;

	Js.JsExpr info(PredicateEqual predicate, Extra extra) {
		return infoImpl(this.convert!T, predicate, extra);
	}

	Js.JsExpr info(PredicateNumber predicate, Extra extra) {
		return infoImpl(this.convert!T, predicate, extra);
	}

	Js.JsExpr info(PredicateTuple predicate, Extra extra) {
		return infoImpl(this.convert!T, predicate, extra);
	}

	Js.JsExpr info(PredicateUnrestricted predicate, Extra extra) {
		return infoImpl(this.convert!T, predicate, extra);
	}
}

class Impl(T : Stage) : Getters!T {
	this(A...)(A arguments) {
		super(arguments);
	}

override:

	string toStringPrecedence(StagePrecedence precedence) {
		return toStringImpl(this, precedence);
	}

	void unify(Stage right, Position position, StageSystem system) {
		return right.unifyMatch(this, position, system);
	}

	void unifyMatch(StageRuntime left, Position position, StageSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyMatch(StageMacro left, Position position, StageSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	void unifyMatch(StageVariable left, Position position, StageSystem system) {
		return unifyImpl(left, this.convert!T, position, system);
	}

	static if (is(T : StageVariable)) {
		Stage substitute(Dictonary!(StageVariableId, Stage) moves) {
			if (id in moves) {
				return moves[id];
			} else {
				return make!StageVariable(id);
			}
		}

		Set!StageVariableId freeVariables() {
			return id.only.rangeToSet;
		}
	} else {
		Stage substitute(Dictonary!(StageVariableId, Stage) moves) {
			return this.destructure!(mapStage!(a => a.substitute(moves), T, make!T));
		}

		Set!StageVariableId freeVariables() {
			alias folder = foldStage!(Set!StageVariableId, emptySet!StageVariableId, mergeSets, T);
			return this.destructure!(mapStage!(a => a.freeVariables, T, folder));
		}
	}

}

class Impl(T : Predicate) : Getters!T if (!isImpl!T) {

	this(A...)(A arguments) {
		super(arguments);
	}

override:

	PredicateId id() {
		return predicateId!T(this);
	}

	static if (is(T : PredicateTuple)) {
		Set!TypeVariableId freeVariables() {
			return type.freeVariables;
		}

		TypeVariableId[] freeVariablesOrdered() {
			return type.freeVariablesOrdered;
		}

		Predicate substitute(Dictonary!(TypeVariableId, Type) moves) {
			return make!T(index, type.substitute(moves));
		}

		Predicate substitute(Dictonary!(RigidVariableId, Type) moves) {
			return make!T(index, type.substitute(moves));
		}

		Predicate substitute(Dictonary!(StageVariableId, Stage) moves) {
			return make!T(index, type.substitute(moves));
		}

	} else {
		Set!TypeVariableId freeVariables() {
			return emptySet!TypeVariableId;
		}

		TypeVariableId[] freeVariablesOrdered() {
			return [];
		}

		Predicate substitute(Dictonary!(TypeVariableId, Type) moves) {
			return this;
		}

		Predicate substitute(Dictonary!(RigidVariableId, Type) moves) {
			return this;
		}

		Predicate substitute(Dictonary!(StageVariableId, Stage) moves) {
			return this;
		}
	}

	void check(Type right, Position position, TypeSystem system) {
		return right.checkDispatch(this, position, system);
	}

	TypeAlgebra[] decompose(Predicate right, Position position) {
		assert(cast(T) right);
		return decomposePredicate(this.convert!T, cast(T) right, position);
	}

	string toString() {
		return toStringImpl(this);
	}

	bool compare(Predicate right) {
		return right.compareDispatch(this);
	}

	bool compareDispatch(PredicateUnrestricted left) {
		return compareImpl(left, this.convert!T);
	}

	bool compareDispatch(PredicateEqual left) {
		return compareImpl(left, this.convert!T);
	}

	bool compareDispatch(PredicateNumber left) {
		return compareImpl(left, this.convert!T);
	}

	bool compareDispatch(PredicateTuple left) {
		return compareImpl(left, this.convert!T);
	}

	import codegen.codegen : Extra;
	import Js = jsast;

	Js.JsExpr typeInfo(Type type, Extra extra) {
		return type.info(this, extra);
	}
}

class Impl(T : TypeAlgebra) : Getters!T {
	this(A...)(A arguments) {
		super(arguments);
	}

override:
	TypeAlgebra substitute(Dictonary!(TypeVariableId, Type) moves) {
		return substituteImpl(this, moves);
	}

	TypeAlgebra substitute(Dictonary!(RigidVariableId, Type) moves) {
		return substituteImpl(this, moves);
	}

	Set!TypeVariableId freeVariables() {
		return freeVariablesImpl(this);
	}

	void reduce(TypeSystem system) {
		return reduceImpl(this, system);
	}

	string toString() {
		return toStringImpl(this);
	}
}

class Impl(T : StageAlgebra) : Getters!T {
	this(A...)(A arguments) {
		super(arguments);
	}

override:
	StageAlgebra substitute(Dictonary!(StageVariableId, Stage) moves) {
		return substituteImpl(this, moves);
	}

	Set!StageVariableId freeVariables() {
		return freeVariablesImpl(this);
	}

	void reduce(StageSystem system) {
		return reduceImpl(this, system);
	}

	string toString() {
		return toStringImpl(this);
	}
}

TypeAlgebra equation(Type left, Type right, Position position) {
	return make!TypeEquation(left, right, position);
}

StageAlgebra equation(Stage left, Stage right, Position position) {
	return make!StageEquation(left, right, position);
}

TypeAlgebra predicateCall(Predicate predicate, Type type, Position position) {
	return make!TypePredicateCall(predicate, type, position);
}

StageAlgebra predicateCall(StagePredicate predicate, Stage type, Position position) {
	return make!StagePredicateCall(predicate, type, position);
}

auto substituteImpl(Id)(TypeEquation that, Dictonary!(Id, Type) moves) {
	return equation(that.left.substitute(moves), that.right.substitute(moves), that.position);
}

auto substituteImpl(Id)(TypePredicateCall that, Dictonary!(Id, Type) moves) {
	return predicateCall(that.predicate.substitute(moves), that.type.substitute(moves), that.position);
}

auto substituteImpl(StageEquation that, Dictonary!(StageVariableId, Stage) moves) {
	return equation(that.left.substitute(moves), that.right.substitute(moves), that.position);
}

auto substituteImpl(StagePredicateCall that, Dictonary!(StageVariableId, Stage) moves) {
	return predicateCall(that.predicate.substitute(moves), that.type.substitute(moves), that.position);
}

auto freeVariablesImpl(TypeEquation that) {
	return freeVariables(that.left, that.right);
}

auto freeVariablesImpl(TypePredicateCall that) {
	return freeVariables(that.predicate, that.type);
}

auto freeVariablesImpl(StageEquation that) {
	return freeVariables(that.left, that.right);
}

auto freeVariablesImpl(StagePredicateCall that) {
	return freeVariables(that.predicate, that.type);
}

auto reduceImpl(TypeEquation that, TypeSystem system) {
	return that.left.unify(that.right, that.position, system);
}

auto reduceImpl(TypePredicateCall that, TypeSystem system) {
	return that.predicate.check(that.type, that.position, system);
}

auto reduceImpl(StageEquation that, StageSystem system) {
	return that.left.unify(that.right, that.position, system);
}

auto reduceImpl(StagePredicateCall that, StageSystem system) {
	return that.predicate.check(that.type, that.position, system);
}

string wrap(string expr, bool when) {
	if (when) {
		return "(" ~ expr ~ ")";
	} else {
		return expr;
	}
}

string toStringImpl(TypeBool that, TypePrecedence) {
	return "boolean";
}

string toStringImpl(TypeChar that, TypePrecedence) {
	return "character";
}

string toStringImpl(TypeInt that, TypePrecedence) {
	return (that.signed ? "integer " : "natural ") ~ that.size.to!string;
}

string toStringImpl(TypeStruct that, TypePrecedence) {
	return "(& " ~ that.values.map!(a => a.toString).joiner(",").array.to!string ~ " &)";
}

string toStringImpl(TypeArray that, TypePrecedence precedence) {
	return ("raw " ~ that.value.toStringPrecedence(TypePrecedence.raw) ~ "[]").wrap(TypePrecedence.raw < precedence);
}

string toStringImpl(TypeFunction that, TypePrecedence precedence) {
	return (that.argument.toStringPrecedence(TypePrecedence.raw) ~ " -> " ~ that.result.toString).wrap(TypePrecedence.arrow < precedence);
}

string toStringImpl(TypeMacro that, TypePrecedence precedence) {
	return (that.argument.toStringPrecedence(TypePrecedence.raw) ~ " ~> " ~ that.result.toString).wrap(TypePrecedence.arrow < precedence);
}

string toStringImpl(TypePointer that, TypePrecedence precedence) {
	return ("raw " ~ that.value.toStringPrecedence(TypePrecedence.raw) ~ "*").wrap(TypePrecedence.raw < precedence);
}

string toStringImpl(TypeOwnPointer that, TypePrecedence precedence) {
	return ("unique " ~ that.value.toStringPrecedence(TypePrecedence.raw) ~ "*").wrap(TypePrecedence.raw < precedence);
}

string toStringImpl(TypeOwnArray that, TypePrecedence precedence) {
	return ("unique " ~ that.value.toStringPrecedence(TypePrecedence.raw) ~ "[]").wrap(TypePrecedence.raw < precedence);
}

string toStringImpl(TypeWorld that, TypePrecedence) {
	return "world";
}

string toStringImpl(TypeVariable that, TypePrecedence) {
	return "v" ~ that.id.raw.to!string;
}

string toStringImpl(TypeVariableRigid that, TypePrecedence) {
	return "<rigid> " ~ that.name;
}

string toStringImpl(PredicateEqual that) {
	return "equal";
}

string toStringImpl(PredicateNumber that) {
	return "number";
}

string toStringImpl(PredicateUnrestricted that) {
	return "unrestricted";
}

string toStringImpl(PredicateTuple that) {
	return that.index.to!string ~ " : " ~ that.type.to!string;
}

string toStringImpl(StageVariable that, StagePrecedence) {
	return "v" ~ that.id.raw.to!string;
}

string toStringImpl(StageRuntime that, StagePrecedence) {
	return "runtime";
}

string toStringImpl(StageMacro that, StagePrecedence precedence) {
	return (that.argument.toStringPrecedence(StagePrecedence.top) ~ " ~*> " ~ that.result.to!string).wrap(StagePrecedence.arrow < precedence);
}

string toStringImpl(TypeEquation that) {
	return that.left.to!string ~ " = " ~ that.right.to!string;
}

string toStringImpl(TypePredicateCall that) {
	return that.predicate.to!string ~ "(" ~ that.type.to!string ~ ")";
}

string toStringImpl(StageEquation that) {
	return that.left.to!string ~ " = " ~ that.right.to!string;
}

string toStringImpl(StagePredicateCall that) {
	return that.predicate.to!string ~ "(" ~ that.type.to!string ~ ")";
}

Tuple!(Variable, bool)[] orderedBindingsImpl(NamedPattern that) {
	return [tuple(make!Variable(that.type, that.name, that.id), that.shadow)];
}

Tuple!(Variable, bool)[] orderedBindingsImpl(TuplePattern that) {
	return that.matches.map!(a => a.orderedBindings).joiner.array;
}

enum Ordering(_ : PredicateEqual) = 0;
enum Ordering(_ : PredicateNumber) = 1;
enum Ordering(_ : PredicateTuple) = 2;
enum Ordering(_ : PredicateUnrestricted) = 3;

bool compareImpl(T1, T2)(T1 left, T2 right) {
	static if (is(T1 == T2)) {
		return compareSame(left, right);
	} else {
		return Ordering!T1 < Ordering!T2;
	}
}

bool compareSame(T)(T left, T right) {
	static if (is(T : PredicateTuple)) {
		return left.index < right.index;
	} else {
		return false;
	}
}

TypeAlgebra[] decomposeEquation(T)(T left, T right, Position position) if (is(T : Type) && !is(T : TypeVariable)) {
	static if (is(T : TypeBool)) {
		return [];
	} else static if (is(T : TypeChar)) {
		return [];
	} else static if (is(T : TypeInt)) {
		if (left.size == right.size && left.signed == right.signed) {
			return [];
		}
		error("Can't match " ~ left.to!string ~ " to " ~ right.to!string, position);
		assert(0);
	} else static if (is(T : TypeStruct)) {
		if (left.values.length == right.values.length) {
			return zip(left.values, right.values).map!(a => equation(a[0], a[1], position)).array;
		}
		error("Can't match " ~ left.to!string ~ " to " ~ right.to!string, position);
		assert(0);
	} else static if (is(T : TypeArray)) {
		return [equation(left.value, right.value, position)];
	} else static if (is(T : TypeFunction)) {
		return [equation(left.result, right.result, position), equation(left.argument, right.argument, position)];
	} else static if (is(T : TypeMacro)) {
		return [equation(left.result, right.result, position), equation(left.argument, right.argument, position)];
	} else static if (is(T : TypePointer)) {
		return [equation(left.value, right.value, position)];
	} else static if (is(T : TypeOwnPointer)) {
		return [equation(left.value, right.value, position)];
	} else static if (is(T : TypeOwnArray)) {
		return [equation(left.value, right.value, position)];
	} else static if (is(T : TypeWorld)) {
		return [];
	}
}

StageAlgebra[] decomposeEquation(T)(T left, T right, Position position) if (is(T : Stage) && !is(T : StageVariable)) {
	static if (is(T : StageRuntime)) {
		return [];
	} else static if (is(T : StageMacro)) {
		return [equation(left.result, right.result, position), equation(left.argument, right.argument, position)];
	}
}

TypeAlgebra[] decomposeCheck(C, T)(C constraint, T type, Position position) if (is(C : Predicate) && is(T : Type) && !is(T : TypeVariable)) {
	static if (is(C : PredicateEqual)) {
		static if (is(T : TypeBool)) {
			return [];
		} else static if (is(T : TypeChar)) {
			return [];
		} else static if (is(T : TypeInt)) {
			return [];
		} else static if (is(T : TypeStruct)) {
			return type.values.map!(inner => predicateCall(make!PredicateEqual, inner, position)).array;
		} else static if (is(T : TypeArray)) {
			return [predicateCall(make!PredicateEqual, type.value, position)];
		} else static if (is(T : TypePointer)) {
			return [];
		}
	} else static if (is(C : PredicateNumber) && is(T : TypeInt)) {
		return [];
	} else static if (is(C : PredicateTuple) && is(T : TypeStruct)) {
		if (constraint.index < type.values.length) {
			auto base = [equation(constraint.type, type.values[constraint.index], position)];
			auto ignored = iota(0, type.values.length).filter!(i => i != constraint.index)
				.map!(i => predicateCall(make!PredicateUnrestricted, type.values[i], position))
				.array;
			return base ~ ignored;
		}

	} else static if (is(C : PredicateUnrestricted)) {
		static if (is(T : TypeBool)) {
			return [];
		} else static if (is(T : TypeChar)) {
			return [];
		} else static if (is(T : TypeInt)) {
			return [];
		} else static if (is(T : TypeStruct)) {
			return type.values.map!(inner => predicateCall(make!PredicateUnrestricted, inner, position)).array;
		} else static if (is(T : TypeArray)) {
			return [];
		} else static if (is(T : TypePointer)) {
			return [];
		} else static if (is(T : TypeFunction)) {
			return [];
		}
		// todo figure out how to make macro non linear
	}
	error("Can't match constraint " ~ constraint.toString ~ " to " ~ type.toString, position);
	assert(0);
}

TypeAlgebra[] decomposePredicate(C)(C left, C right, Position position) if (is(C : Predicate)) {
	static if (is(C : PredicateEqual)) {
		return [];
	} else static if (is(C : PredicateNumber)) {
		return [];
	} else static if (is(C : PredicateTuple)) {
		assert(left.index == right.index);
		return [equation(left.type, right.type, position)];
	} else static if (is(C : PredicateUnrestricted)) {
		return [];
	}
}

alias TypeUnifier = Unifier!(make, decomposeEquation, decomposeCheck, TypeVariableId, TypeVariable, RigidVariableId, RigidContextId, TypeVariableRigid, Type, PredicateId, Predicate, TypeAlgebra, TypeEquation, TypePredicateCall, TypeSystem, StageSystem, StageEquation);
alias StageUnifier = Unifier!(make, decomposeEquation, void, StageVariableId, StageVariable, void, void, void, Stage, StagePredicateId, StagePredicate, StageAlgebra, StageEquation, StagePredicateCall, StageSystem, void, void);

void unifyAll(TypeSystem system) {
	TypeUnifier.unifyAll(system);
}

void unifyAll(StageSystem system) {
	return StageUnifier.unifyAll(system);
}

void unifyImpl(T1, T2)(T1 left, T2 right, Position position, TypeSystem system) if (is(T1 : Type) && is(T2 : Type)) {
	TypeUnifier.unifyImpl(left, right, position, system);
}

void checkImpl(C, T)(C predicate, T type, Position position, TypeSystem system) {
	TypeUnifier.checkImpl(predicate, type, position, system);
}

void unifyImpl(T1, T2)(T1 left, T2 right, Position position, StageSystem system) if (is(T1 : Stage) && is(T2 : Stage)) {
	StageUnifier.unifyImpl(left, right, position, system);
}

auto genericMap(alias f, T)(T[] that) {
	return that.map!f.array;
}

auto genericMap(alias f, K, V)(Dictonary!(K, V) that) {
	return that.mapValues!f;
}

auto genericMap(alias f, T)(Lazy!T that) {
	return defer(() => f(that.get));
}

Set!TypeVariableId freeVariables(T)(T item) if (is(T : Type) || is(T : Predicate) || is(T : TypeAlgebra)) {
	return item.freeVariables;
}

Set!StageVariableId freeVariables(T)(T item) if (is(T : Stage) || is(T : StagePredicate) || is(T : StageAlgebra)) {
	return item.freeVariables;
}

auto freeVariables(R)(R data) if (isInputRange!R) {
	auto empty = typeof(.freeVariables(data.front)).init;
	return data.map!(a => a.freeVariables)
		.fold!mergeSets(empty);
}

auto freeVariables(T...)(T arguments) if (T.length > 1) {
	return mergeSets(arguments[0 .. $ - 1].freeVariables, arguments[$ - 1].freeVariables);
}

auto freeVariables(K, V)(Dictonary!(K, V) data) {
	return data.byValue.freeVariables;
}

auto substitute(T, M)(T equation, M moves) if (!__traits(hasMember, T, "substitute")) {
	return genericMap!(a => a.substitute(moves))(equation);
}

auto reduceMacros(T)(T that) if (!__traits(hasMember, T, "reduceMacros")) {
	return genericMap!(a => a.reduceMacros)(that);
}

auto alphaConvert(T)(T that) if (!__traits(hasMember, T, "alphaConvert")) {
	return genericMap!(a => a.alphaConvert)(that);
}

template constantFunctorTerm(alias t, alias c) {
	auto constantFunctorTerm(T, A...)(T type, A arguments) {
		return c(t(type), arguments);
	}
}

template constantFunctor(alias c) {
	auto constantFunctor(A...)(A arguments) {
		return c(arguments);
	}
}

alias mapTerm(alias f, T, alias c) = mapTermAll!(f, a => a, a => a, a => a, T, c);

// map the base functor and pass it long a continuation
// f -> terms, t -> types, pa -> pattern, pr -> predicate
alias mapTermAll(alias f, alias t, alias pa, alias pr, _ : SymbolForwardReference, alias c) = constantFunctorTerm!(t, c);
template mapTermAll(alias f, alias t, alias pa, alias pr, _ : SymbolReference, alias c) {
	auto mapTermAll(F, T, P)(T type, string name, Linkage linkage, SymbolId id, Lazy!F source, Tuple!(T, P)[] dictonaries) {
		return c(t(type), name, linkage, id, defer(() => f(source.get)), dictonaries.map!(a => tuple(t(a[0]), pr(a[1]))).array);
	}
}

template mapTermAll(alias f, alias t, alias pa, alias pr, _ : ExternJs, alias c) {
	auto mapTermAll(T, P)(T type, string name, Tuple!(T, P)[] dictonaries) {
		return c(t(type), name, dictonaries.map!(a => tuple(t(a[0]), pr(a[1]))).array);
	}
}

template mapTermAll(alias f, alias t, alias pa, alias pr, _ : MacroFunctionLiteral, alias c) {
	auto mapTermAll(F, T)(T type, Argument argument, F text) {
		return c(t(type), argument, f(text));
	}
}

alias mapTermAll(alias f, alias t, alias pa, alias pr, _ : Variable, alias c) = constantFunctorTerm!(t, c);
template mapTermAll(alias f, alias t, alias pa, alias pr, _ : VariableDefinition, alias c) {
	auto mapTermAll(F, T, PA)(T type, PA variable, F value, F last) {
		return c(t(type), pa(variable), f(value), f(last));
	}
}

template mapTermAll(alias f, alias t, alias pa, alias pr, _ : Call, alias c) {
	auto mapTermAll(F, T)(T type, F calle, F argument) {
		return c(t(type), f(calle), f(argument));
	}
}

template mapTermAll(alias f, alias t, alias pa, alias pr, _ : MacroCall, alias c) {
	auto mapTermAll(F, T)(T type, F calle, F argument) {
		return c(t(type), f(calle), f(argument));
	}
}

template mapTermAll(alias f, alias t, alias pa, alias pr, _ : If, alias c) {
	auto mapTermAll(F, T)(T type, F cond, F yes, F no) {
		return c(t(type), f(cond), f(yes), f(no));
	}
}

alias mapTermAll(alias f, alias t, alias pa, alias pr, _ : TupleIndex, alias c) = constantFunctorTerm!(t, c);
template mapTermAll(alias f, alias t, alias pa, alias pr, _ : TupleIndexAddress, alias c) {
	auto mapTermAll(T)(T type, uint index, T context) {
		return c(t(type), index, t(context));
	}
}

alias mapTermAll(alias f, alias t, alias pa, alias pr, _ : IntLit, alias c) = constantFunctorTerm!(t, c);
alias mapTermAll(alias f, alias t, alias pa, alias pr, _ : CharLit, alias c) = constantFunctorTerm!(t, c);
alias mapTermAll(alias f, alias t, alias pa, alias pr, _ : BoolLit, alias c) = constantFunctorTerm!(t, c);
template mapTermAll(alias f, alias t, alias pa, alias pr, _ : TupleLit, alias c) {
	auto mapTermAll(F, T)(T type, F[] values) {
		return c(t(type), values.map!(a => f(a)).array);
	}
}

alias mapTermAll(alias f, alias t, alias pa, alias pr, _ : StringLit, alias c) = constantFunctorTerm!(t, c);
template mapTermAll(alias f, alias t, alias pa, alias pr, _ : ArrayLit, alias c) {
	auto mapTermAll(F, T)(T type, F[] values) {
		return c(t(type), values.map!(a => f(a)).array);
	}
}

alias mapPattern(alias f, T, alias c) = mapPatternAll!(f, a => a, T, c);

template mapPatternAll(alias f, alias t, _ : NamedPattern, alias c) {
	auto mapPatternAll(T)(T type, VariableId id, string name, bool shadow) {
		return c(t(type), id, name, shadow);
	}
}

template mapPatternAll(alias f, alias t, _ : TuplePattern, alias c) {
	auto mapPatternAll(F, T)(T type, F[] matches) {
		return c(t(type), matches.map!(a => f(a)).array);
	}
}

template constantFunctorType(alias s, alias c) {
	auto constantFunctorType(S, A...)(S type, A arguments) {
		return c(s(type), arguments);
	}
}

alias mapType(alias f, T, alias c) = mapTypeAll!(f, a => a, T, c);
alias mapTypeAll(alias f, alias s, _ : TypeVariable, alias c) = constantFunctorType!(s, c);
alias mapTypeAll(alias f, alias s, _ : TypeVariableRigid, alias c) = constantFunctorType!(s, c);
alias mapTypeAll(alias f, alias s, _ : TypeBool, alias c) = constantFunctorType!(s, c);
alias mapTypeAll(alias f, alias s, _ : TypeChar, alias c) = constantFunctorType!(s, c);
alias mapTypeAll(alias f, alias s, _ : TypeInt, alias c) = constantFunctorType!(s, c);
template mapTypeAll(alias f, alias s, _ : TypeStruct, alias c) {
	auto mapTypeAll(T, S)(S type, T[] values) {
		return c(s(type), values.map!(a => f(a)).array);
	}
}

template mapTypeAll(alias f, alias s, _ : TypeFunction, alias c) {
	auto mapTypeAll(T, S)(S type, T result, T argument) {
		return c(s(type), f(result), f(argument));
	}
}

template mapTypeAll(alias f, alias s, _ : TypeMacro, alias c) {
	auto mapTypeAll(T, S)(S type, T result, T argument) {
		return c(s(type), f(result), f(argument));
	}
}

template mapTypeAll(alias f, alias s, _ : TypeArray, alias c) {
	auto mapTypeAll(T, S)(S type, T value) {
		return c(s(type), f(value));
	}
}

template mapTypeAll(alias f, alias s, _ : TypeOwnArray, alias c) {
	auto mapTypeAll(T, S)(S type, T value) {
		return c(s(type), f(value));
	}
}

template mapTypeAll(alias f, alias s, _ : TypePointer, alias c) {
	auto mapTypeAll(T, S)(S type, T value) {
		return c(s(type), f(value));
	}
}

template mapTypeAll(alias f, alias s, _ : TypeOwnPointer, alias c) {
	auto mapTypeAll(T, S)(S type, T value) {
		return c(s(type), f(value));
	}
}

alias mapTypeAll(alias f, alias s, _ : TypeWorld, alias c) = constantFunctorType!(s, c);

alias mapStage(alias f, _ : StageRuntime, alias c) = constantFunctor!c;
template mapStage(alias f, _ : StageMacro, alias c) {
	auto mapStage(A)(A result, A argument) {
		return c(f(result), f(argument));
	}
}

A foldType(A, alias mempty, alias mappend, _ : TypeBool)(Stage type) {
	return mempty;
}

A foldType(A, alias mempty, alias mappend, _ : TypeChar)(Stage type) {
	return mempty;
}

A foldType(A, alias mempty, alias mappend, _ : TypeInt)(Stage type, uint size, bool signed) {
	return mempty;
}

A foldType(A, alias mempty, alias mappend, _ : TypeStruct)(Stage type, A[] types) {
	return types.fold!mappend(mempty);
}

A foldType(A, alias mempty, alias mappend, _ : TypeFunction)(Stage type, A result, A argument) {
	return mappend(argument, result);
}

A foldType(A, alias mempty, alias mappend, _ : TypeMacro)(Stage type, A result, A argument) {
	return mappend(argument, result);
}

A foldType(A, alias mempty, alias mappend, _ : TypeArray)(Stage type, A value) {
	return value;
}

A foldType(A, alias mempty, alias mappend, _ : TypeOwnArray)(Stage type, A value) {
	return value;
}

A foldType(A, alias mempty, alias mappend, _ : TypePointer)(Stage type, A value) {
	return value;
}

A foldType(A, alias mempty, alias mappend, _ : TypeOwnPointer)(Stage type, A value) {
	return value;
}

A foldType(A, alias mempty, alias mappend, _ : TypeWorld)(Stage type) {
	return mempty;
}

A foldStage(A, alias mempty, alias mappend, _ : StageRuntime)() {
	return mempty;
}

A foldStage(A, alias mempty, alias mappend, _ : StageMacro)(A result, A argument) {
	return mappend(result, argument);
}
