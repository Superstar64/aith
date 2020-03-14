/+
	Copyright (C) 2020  Freddy Angel Cubas "Superstar64"
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

import misc.position;

static import Semantic = semantic.ast;

class Module {
	ModuleVarDef[] symbols;
}

interface Node {
	Position position();
}

interface ModuleVarDef {
	Position position();
	string[] polymorphicVariables();
	string name();
	Expression explicitType(); //nullable
	Expression value();
}

interface Expression : Node {
	Pattern patternMatch();
}

interface Assign : Expression {
	Position position();
	Expression left();
	Expression right();
}

interface VariableDef : Expression {
	Position position();
	Pattern variable();
	Expression value();
	Expression last();
}

interface TypeBool : Expression {
	Position position();
}

interface TypeChar : Expression {
	Position position();
}

interface TypeInt : Expression {
	Position position();
	int size();
	bool signed();
}

interface Import : Expression {
	Position position();
	Semantic.Module mod();
}

interface IntLit : Expression {
	Position position();
	BigInt value();
}

interface CharLit : Expression {
	Position position();
	dchar value();
}

interface BoolLit : Expression {
	Position position();
	bool yes();
}

interface TypeTuple : Expression {
	Position position();
	Expression[] values();
}

interface TupleLit : Expression {
	Position position();
	Expression[] values();
}

interface Variable : Expression {
	Position position();
	string name();
}

interface If : Expression {
	Position position();
	Expression cond();
	Expression yes();
	Expression no();
}

interface While : Expression {
	Position position();
	Expression cond();
	Expression state();
}

interface New : Expression {
	Position position();
	Expression value();
}

interface NewArray : Expression {
	Position position();
	Expression length();
	Expression value();
}

interface Cast : Expression {
	Position position();
	Expression type();
	Expression value();
}

interface Infer : Expression {
	Position position();
	Expression type();
	Expression value();
}

interface Length : Expression {
	Position position();
}

interface UseSymbol : Expression {
	Position position();
	Expression value();
	string index();
}

interface Index : Expression {
	Position position();
	Expression array();
	Expression index();
}

interface IndexAddress : Expression {
	Position position();
	Expression array();
	Expression index();
}

interface TupleIndex : Expression {
	Position position();
	Expression tuple();
	uint index();
}

interface TupleIndexAddress : Expression {
	Position position();
	Expression tuple();
	uint index();
}

interface Call : Expression {
	Position position();
	Expression calle();
	Expression argument();
}

interface Slice : Expression {
	Position position();
	Expression array();
	Expression left();
	Expression right();
}

interface Binary(string T) : Expression if (["*", "/", "%", "+", "-", "~", "==", "!=", "<=", ">=", "<", ">", "&&", "||", "->"].canFind(T)) {
	Position position();
	Expression left();
	Expression right();
}

interface Prefix(string T) : Expression if (["-", "*", "!"].canFind(T)) {
	Position position();
	Expression value();
}

interface Postfix(string T) : Expression if (["(*)", "[*]"].canFind(T)) {
	Position position();
	Expression value();
}

interface Pattern : Node {
}

interface NamedArgument : Pattern {
	Position position();
	string name();
}

interface TupleArgument : Pattern {
	Position position();
	Pattern[] matches();
}

interface FuncLit : Expression {
	Position position();
	Expression text();
	Pattern argument();
}

interface StringLit : Expression {
	Position position();
	string value();
}

interface ArrayLit : Expression {
	Position position();
	Expression[] values();
}

interface ExternJs : Expression {
	Position position();
	string name();
}
