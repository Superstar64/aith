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
import misc.nonstrict;

class Module {
	ModuleVarDef[] symbols;
}

interface Node {
	import Semantic = semantic.ast;
	import semantic.semantic : Context;

	Position position();
	Semantic.Expression semanticMain(Context context);
}

enum SymbolSort {
	symbol,
	generative,
	inline,
	external
}

interface ModuleVarDef {
	Position position();
	string name();
	SymbolSort sort();
	Expression explicitType(); //nullable
	Expression value();
}

interface Expression : Node {
	Pattern patternMatch();
}

interface VariableDefinition : Expression {
	Position position();
	Pattern variable();
	Expression value();
	Expression last();
}

interface Run : Expression {
	Position position();
	Expression value();
	Expression last();
}

interface ConstraintTuple : Expression {
	Position position();
	uint index();
	Expression type();
}

interface Import : Expression {
	Position position();
	Lazy!Module value();
}

struct ForallBinding {
	string name;
	Expression[] predicates;
}

interface Forall : Expression {
	Position position();
	ForallBinding[] bindings();
	Expression value();
}

interface FunctionLiteral : Expression {
	Position position();
	Expression text();
	Pattern argument();
}

interface Call : Expression {
	Position position();
	Expression calle();
	Expression argument();
}

interface FromRuntime : Expression {
	Position position();
	Expression value();
}

interface MacroFunctionLiteral : Expression {
	Position position();
	Expression text();
	string argument();
	bool shadow();
}

interface NamedArgument : Pattern {
	Position position();
	string name();
	bool shadow();
}

interface TupleArgument : Pattern {
	Position position();
	Pattern[] matches();
}

interface IntLit : Expression {
	Position position();
	BigInt value();
}

interface CharLit : Expression {
	Position position();
	dchar value();
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
	bool shadow();
}

interface If : Expression {
	Position position();
	Expression cond();
	Expression yes();
	Expression no();
}

interface Infer : Expression {
	Position position();
	Expression type();
	Expression value();
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

interface Slice : Expression {
	Position position();
	Expression array();
	Expression left();
	Expression right();
}

interface Binary(string T) : Expression if (["*", "/", "%", "+", "-", "==", "!=", "<=", ">=", "<", ">", "&&", "||", "->", "<-", "~>"].canFind(T)) {
	Position position();
	Expression left();
	Expression right();
}

interface Prefix(string T) : Expression if (["-", "*", "!"].canFind(T)) {
	Position position();
	Expression value();
}

interface Do : Expression {
	Position position();
	Expression value();
}

interface Try : Expression {
	Position position();
	Expression value();
}

interface TypePointer(string type) : Expression if (["raw", "unique"].canFind(type)) {
	Position position();
	Expression value();
}

interface TypeArray(string type) : Expression if (["raw", "unique"].canFind(type)) {
	Position position();
	Expression value();
}

interface Pattern : Node {
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
