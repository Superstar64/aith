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
module parser.ast;

import std.algorithm;
import std.bigint;

import misc.position;

class Module {
	ModuleBinding[] bindings;
}

abstract class Node {
	import Semantic = semantic.ast;
	import semantic.semantic : Context;

	Position position;

	this(Position position) {
		this.position = position;
	}

	Semantic.Expression semanticMain(Context context);
}

enum BindingSort {
	symbol,
	generative,
	inline,
	overload
}

abstract class ModuleBinding {
	Position position;
	string name;
	BindingSort sort;
	Expression explicitType; //nullable
	string classTypeVariable; // only for overloaded classes
	Expression classTypeScheme; //nullable
	Expression value;
	this(Position position, string name, BindingSort sort, Expression explicitType, string classTypeVariable, Expression classTypeScheme, Expression value) {
		this.position = position;
		this.name = name;
		this.sort = sort;
		this.explicitType = explicitType;
		this.classTypeVariable = classTypeVariable;
		this.classTypeScheme = classTypeScheme;
		this.value = value;
	}
}

abstract class Expression : Node {
	Pattern patternMatch();
	this(Position position) {
		super(position);
	}
}

abstract class VariableDefinition : Expression {
	Pattern variable;
	Expression value;
	Expression last;
	this(Position position, Pattern variable, Expression value, Expression last) {
		super(position);
		this.variable = variable;
		this.value = value;
		this.last = last;
	}
}

abstract class Run : Expression {
	Expression value;
	Expression last;
	this(Position position, Expression value, Expression last) {
		super(position);
		this.value = value;
		this.last = last;
	}
}

abstract class ConstraintTuple : Expression {
	uint index;
	Expression type;
	this(Position position, uint index, Expression type) {
		super(position);
		this.index = index;
		this.type = type;
	}
}

abstract class Import : Expression {
	Module delegate() value;
	this(Position position, Module delegate() value) {
		super(position);
		this.value = value;
	}
}

struct ForallBinding {
	string name;
	Expression[] predicates;
}

abstract class Forall : Expression {
	ForallBinding[] bindings;
	Expression value;
	this(Position position, ForallBinding[] bindings, Expression value) {
		super(position);
		this.bindings = bindings;
		this.value = value;
	}
}

abstract class FunctionLiteral : Expression {
	Expression text;
	Pattern argument;
	this(Position position, Expression text, Pattern argument) {
		super(position);
		this.text = text;
		this.argument = argument;
	}
}

abstract class Call : Expression {
	Expression calle;
	Expression argument;
	this(Position position, Expression calle, Expression argument) {
		super(position);
		this.calle = calle;
		this.argument = argument;
	}
}

abstract class FromRuntime : Expression {
	Expression value;
	this(Position position, Expression value) {
		super(position);
		this.value = value;
	}
}

abstract class MacroFunctionLiteral : Expression {
	Expression text;
	string argument;
	bool shadow;
	this(Position position, Expression text, string argument, bool shadow) {
		super(position);
		this.text = text;
		this.argument = argument;
		this.shadow = shadow;
	}
}

abstract class NamedArgument : Pattern {
	string name;
	bool shadow;
	this(Position position, string name, bool shadow) {
		super(position);
		this.name = name;
		this.shadow = shadow;
	}
}

abstract class TupleArgument : Pattern {
	Pattern[] matches;
	this(Position position, Pattern[] matches) {
		super(position);
		this.matches = matches;
	}
}

abstract class IntLit : Expression {
	BigInt value;
	this(Position position, BigInt value) {
		super(position);
		this.value = value;
	}
}

abstract class CharLit : Expression {
	dchar value;
	this(Position position, dchar value) {
		super(position);
		this.value = value;
	}
}

abstract class TypeTuple : Expression {
	Expression[] values;
	this(Position position, Expression[] values) {
		super(position);
		this.values = values;
	}
}

abstract class TupleLit : Expression {
	Expression[] values;
	this(Position position, Expression[] values) {
		super(position);
		this.values = values;
	}
}

abstract class Variable : Expression {
	string name;
	bool shadow;
	this(Position position, string name, bool shadow) {
		super(position);
		this.name = name;
		this.shadow = shadow;
	}
}

abstract class If : Expression {
	Expression cond;
	Expression yes;
	Expression no;
	this(Position position, Expression cond, Expression yes, Expression no) {
		super(position);
		this.cond = cond;
		this.yes = yes;
		this.no = no;
	}
}

abstract class Infer : Expression {
	Expression type;
	Expression value;
	this(Position position, Expression type, Expression value) {
		super(position);
		this.type = type;
		this.value = value;
	}
}

abstract class UseSymbol : Expression {
	Expression value;
	string index;
	this(Position position, Expression value, string index) {
		super(position);
		this.value = value;
		this.index = index;
	}
}

abstract class Index : Expression {
	Expression array;
	Expression index;
	this(Position position, Expression array, Expression index) {
		super(position);
		this.array = array;
		this.index = index;
	}
}

abstract class IndexAddress : Expression {
	Expression array;
	Expression index;
	this(Position position, Expression array, Expression index) {
		super(position);
		this.array = array;
		this.index = index;
	}
}

abstract class TupleIndex : Expression {
	Expression tuple;
	uint index;
	this(Position position, Expression tuple, uint index) {
		super(position);
		this.tuple = tuple;
		this.index = index;
	}
}

abstract class TupleIndexAddress : Expression {
	Expression tuple;
	uint index;
	this(Position position, Expression tuple, uint index) {
		super(position);
		this.tuple = tuple;
		this.index = index;
	}
}

abstract class Slice : Expression {
	Expression array;
	Expression left;
	Expression right;
	this(Position position, Expression array, Expression left, Expression right) {
		super(position);
		this.array = array;
		this.left = left;
		this.right = right;
	}
}

abstract class Binary(string T) : Expression if (["*", "/", "%", "+", "-", "==", "!=", "<=", ">=", "<", ">", "&&", "||", "->", "<-", "~>", "|||"].canFind(T)) {
	Expression left;
	Expression right;
	this(Position position, Expression left, Expression right) {
		super(position);
		this.left = left;
		this.right = right;
	}
}

abstract class Prefix(string T) : Expression if (["-", "*", "!"].canFind(T)) {
	Expression value;
	this(Position position, Expression value) {
		super(position);
		this.value = value;
	}
}

abstract class Do : Expression {
	Expression value;
	this(Position position, Expression value) {
		super(position);
		this.value = value;
	}
}

abstract class Try : Expression {
	Expression value;
	this(Position position, Expression value) {
		super(position);
		this.value = value;
	}
}

abstract class TypePointer(string type) : Expression if (["raw", "unique"].canFind(type)) {
	Expression value;
	this(Position position, Expression value) {
		super(position);
		this.value = value;
	}
}

abstract class TypeArray(string type) : Expression if (["raw", "unique"].canFind(type)) {
	Expression value;
	this(Position position, Expression value) {
		super(position);
		this.value = value;
	}
}

abstract class Pattern : Node {
	this(Position position) {
		super(position);
	}
}

abstract class StringLit : Expression {
	string value;
	this(Position position, string value) {
		super(position);
		this.value = value;
	}
}

abstract class ArrayLit : Expression {
	Expression[] values;
	this(Position position, Expression[] values) {
		super(position);
		this.values = values;
	}
}

abstract class Requirement : Expression {
	Expression value;
	this(Position position, Expression value) {
		super(position);
		this.value = value;
	}
}

abstract class ExternJs : Expression {
	string name;
	Expression scheme;
	this(Position position, string name, Expression scheme) {
		super(position);
		this.name = name;
		this.scheme = scheme;
	}
}

abstract class Instance : Expression {
	Expression type;
	Expression term;
	this(Position position, Expression type, Expression term) {
		super(position);
		this.type = type;
		this.term = term;
	}
}
