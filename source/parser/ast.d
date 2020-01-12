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

interface Node {
	ref Position position();
}

interface Statement : Node {
}

interface Assign : Statement {
ref:
	override Position position();
	Expression left();
	Expression right();
}

struct Modifier {
	bool visible;
	bool global;
}

interface VariableDef : Statement {
ref:
	Position position();
	Pattern variable();
	Expression value();
}

interface ModuleVarDef {
	alias modifier this;
ref:
	Modifier modifier();
	Position position();
	string name();
	Expression explicitType(); //nullable
	Expression value();
}

interface Expression : Statement {
	Pattern patternMatch();
}

interface TypeBool : Expression {
ref:
	Position position();
}

interface TypeChar : Expression {
ref:
	Position position();
}

interface TypeInt : Expression {
ref:
	Position position();
	int size();
	bool signed();
}

interface Import : Expression {
ref:
	Position position();
	Semantic.Module mod();
}

interface IntLit : Expression {
ref:
	Position position();
	BigInt value();
}

interface CharLit : Expression {
ref:
	Position position();
	dchar value();
}

interface BoolLit : Expression {
ref:
	Position position();
	bool yes();
}

interface TypeTuple : Expression {
ref:
	Position position();
	Expression[] values();
}

interface TupleLit : Expression {
ref:
	Position position();
	Expression[] values();
}

interface Variable : Expression {
ref:
	Position position();
	string name();
}

interface If : Expression {
ref:
	Position position();
	Expression cond();
	Expression yes();
	Expression no();
}

interface While : Expression {
ref:
	Position position();
	Expression cond();
	Expression state();
}

interface New : Expression {
ref:
	Position position();
	Expression value();
}

interface NewArray : Expression {
ref:
	Position position();
	Expression length();
	Expression value();
}

interface Cast : Expression {
ref:
	Position position();
	Expression type();
	Expression value();
}

interface Infer : Expression {
ref:
	Position position();
	Expression type();
	Expression value();
}

interface Length : Expression {
ref:
	Position position();
}

interface UseSymbol : Expression {
ref:
	Position position();
	Expression value();
	string index();
}

interface Index : Expression {
ref:
	Position position();
	Expression array();
	Expression index();
}

interface IndexAddress : Expression {
ref:
	Position position();
	Expression array();
	Expression index();
}

interface TupleIndex : Expression {
ref:
	Position position();
	Expression tuple();
	uint index();
}

interface TupleIndexAddress : Expression {
ref:
	Position position();
	Expression tuple();
	uint index();
}

interface Call : Expression {
ref:
	Position position();
	Expression calle();
	Expression argument();
}

interface Slice : Expression {
ref:
	Position position();
	Expression array();
	Expression left();
	Expression right();
}

interface Binary(string T) : Expression if (["*", "/", "%", "+", "-", "~", "==", "!=", "<=", ">=", "<", ">", "&&", "||", "->"].canFind(T)) {
ref:
	Position position();
	Expression left();
	Expression right();
}

interface Prefix(string T) : Expression if (["-", "*", "!"].canFind(T)) {
ref:
	Position position();
	Expression value();
}

interface Postfix(string T) : Expression if (["(*)", "[*]"].canFind(T)) {
ref:
	Position position();
	Expression value();
}

interface Scope : Expression {
ref:
	Position position();
	Statement[] states();
	Expression last(); //nullable
}

interface Pattern : Node {
}

interface NamedArgument : Pattern {
ref:
	Position position();
	string name();
}

interface TupleArgument : Pattern {
ref:
	Position position();
	Pattern[] matches();
}

interface FuncLit : Expression {
ref:
	Position position();
	Expression text();
	Pattern argument();
}

interface StringLit : Expression {
ref:
	Position position();
	string value();
}

interface ArrayLit : Expression {
ref:
	Position position();
	Expression[] values();
}

interface ExternJs : Expression {
ref:
	Position position();
	string name();
}
