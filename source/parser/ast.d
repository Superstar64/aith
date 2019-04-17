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
module parser.ast;

import std.algorithm;
import std.bigint;
import misc;

static import Semantic = semantic.ast;

class Module {
	ModuleVarDef[] symbols;
}

abstract class Node {
	Position position;
}

abstract class Statement : Node {
}

class Assign : Statement {
	Expression left;
	Expression right;
}

abstract class VarDef : Statement {
	bool manifest;
	string name;
	Expression explicitType; //nullable
	Expression value;
}

struct Modifier {
	bool visible;
}

class ScopeVarDef : VarDef {
}

class ModuleVarDef : VarDef {
	Modifier modifier;
	alias modifier this;
}

abstract class Expression : Statement {
}

class TypeBool : Expression {
}

class TypeChar : Expression {
}

class TypeInt : Expression {
	int size;
	bool signed;
}

class Import : Expression {
	Semantic.Module mod;
}

class IntLit : Expression {
	BigInt value;
}

class CharLit : Expression {
	dchar value;
}

class BoolLit : Expression {
	bool yes;
}

class TypeTuple : Expression {
	Expression value;
}

class TupleLit : Expression {
	Expression[] values;
}

class Variable : Expression {
	string name;
}

class FuncArgument : Expression {
}

class If : Expression {
	Expression cond;
	Expression yes;
	Expression no;
}

class While : Expression {
	Expression cond;
	Expression state;
}

class New : Expression {
	Expression value;
}

class NewArray : Expression {
	Expression length;
	Expression value;
}

class Cast : Expression {
	Expression type;
}

class Infer : Expression {
	Expression type;
}

class Dot : Expression {
	Expression value;
	string index;
}

class UseSymbol : Expression {
	Expression value;
	string index;
}

class Index : Expression {
	Expression array;
	Expression index;
}

class TupleIndex : Expression {
	Expression tuple;
	uint total;
	uint index;
}

class Call : Expression {
	Expression calle;
	Expression argument;
}

class Slice : Expression {
	Expression array;
	Expression left;
	Expression right;
}

class Binary(string T) : Expression
		if ([
				"*", "/", "%", "+", "-", "~", "==", "!=", "<=", ">=", "<", ">",
				"&&", "||", "->"
			].canFind(T)) {
	Expression left;
	Expression right;
}

class Prefix(string T) : Expression if (["-", "*", "&", "!"].canFind(T)) {
	Expression value;
}

class Postfix(string T) : Expression if (["(*)", "[*]"].canFind(T)) {
	Expression value;
}

class Scope : Expression {
	Statement[] states;
	Expression last; //nullable
}

class FuncLit : Expression {
	Expression text;
}

class StringLit : Expression {
	string value;
}

class ArrayLit : Expression {
	Expression[] values;
}

class ExternJs : Expression {
	string name;
}
