module codegen.ast;
public import genericast;

import std.bigint;

import misc;
import jsast;
import codegen.codegen : Extra;

interface Module : Jsonable {
	Symbol[string] exports();
}

interface Expression : Jsonable {
	Type type();

	JsExpr generateJs(JsScope depend, Extra extra);
	void generateJsVarDef(JsVariable target, JsScope depend, Extra extra);
	void generateJsVar(JsVariable target, JsScope depend, Extra extra);

	Symbol[SymbolId] symbols();
}

interface Symbol : Expression {
	string name();
	bool strong();
	SymbolId id();
	Symbol[SymbolId] dependants();

	JsExpr generateSymbol(JsScope, Extra);
}

interface Pattern : Jsonable {
	Type type();
}

T castTo(T)(Pattern pattern) {
	return cast(T) pattern;
}

interface NamedPattern : Pattern {
	Type type();
	Variable argument();
}

interface TuplePattern : Pattern {
	Type type();
	Pattern[] matches();
}

interface FunctionLiteral : Symbol {
	Type type();
	string name();
	bool strong();
	SymbolId id();
	Pattern argument();
	Lazy!Expression text();
}

interface Var : Expression {
	string name();
	VarId id();
}

interface Variable : Var {
	Type type();
	string name();
	VarId id();
}

interface VariableDef : Expression {
	Type type();
	Pattern variable();
	Expression value();
	Expression last();
}

interface IntLit : Expression {
	Type type();
	BigInt value();
}

interface CharLit : Expression {
	Type type();
	dchar value();
}

interface BoolLit : Expression {
	Type type();
	bool yes();
}

interface TupleLit : Expression {
	Type type();
	Expression[] values();
}

interface If : Expression {
	Type type();
	Expression cond();
	Expression yes();
	Expression no();
}

interface While : Expression {
	Type type();
	Expression cond();
	Expression state();
}

interface New : Expression {
	Type type();
	Expression value();
}

interface NewArray : Expression {
	Type type();
	Expression length();
	Expression value();
}

interface CastInteger : Expression {
	Type type();
	Expression value();
}

interface Length : Expression {
	Type type();
}

interface Index : Expression {
	Type type();
	Expression array();
	Expression index();
}

interface IndexAddress : Expression {
	Type type();
	Expression array();
	Expression index();
}

interface TupleIndex : Expression {
	Type type();
	Expression tuple();
	uint index();
}

interface TupleIndexAddress : Expression {
	Type type();
	Expression tuple();
	uint index();
}

interface Call : Expression {
	Type type();
	Expression calle();
	Expression argument();
}

interface Slice : Expression {
	Type type();
	Expression array();
	Expression left();
	Expression right();
}

interface Binary(string op) : Expression {
	Type type();
	Expression left();
	Expression right();
}

interface Prefix(string op) : Expression {
	Type type();
	Expression value();
}

interface Deref : Expression {
	Type type();
	Expression value();
}

interface Scope : Expression {
	Type type();
	Expression pass();
	Expression last();
}

interface Assign : Expression {
	Type type();
	Expression left();
	Expression right();
	Expression last();
}

interface StringLit : Expression {
	Type type();
	string value();
}

interface ArrayLit : Expression {
	Type type();
	Expression[] values();
}

interface ExternJs : Expression {
	Type type();
	string name();
}

interface Type : Jsonable {
	string mangle();
	JsExpr runtimeInfo();
}

T castTo(T)(Type type) {
	return cast(T) type;
}

interface TypeChar : Type {
}

interface TypeBool : Type {
}

interface TypeInt : Type {
	uint size();
	bool signed();
}

interface TypeStruct : Type {
	Type[] values();
}

interface TypeArray : Type {
	Type array();
}

interface TypePointer : Type {
	Type value();
}

interface TypeFunction : Type {
	Type result();
	Type argument();
}

bool isEmptyTuple(Type type) {
	auto tuple = type.castTo!TypeStruct;
	return tuple && tuple.values.length == 0;
}
