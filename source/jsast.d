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
module jsast;

import std.algorithm;
import std.range;
import std.typecons;
import std.conv;

import std.range.interfaces;

import misc.container;

auto increase(ref uint indent) {
	indent += 4;
}

auto decrease(ref uint indent) {
	indent -= 4;
}

auto line(scope void delegate(const(char)[]) result, uint indent) {
	result("\n");
	foreach (_; 0 .. indent) {
		result(" ");
	}
}

struct JsContext {
	Dictonary!(string, JsVariable) variables;
	Dictonary!(JsVariable, string) names;

	JsContext insert(JsVariable variable) {
		auto clone = this;
		return clone.insertImpl(variable);
	}

	JsContext insertImpl(JsVariable variable) {
		foreach (name; variable.convention) {
			if (!(name in variables)) {
				variables[name] = variable;
				names[variable] = name;
				return this;
			}
		}
		assert(0);
	}
}

class JsVariable : JsExpr, JsPattern {
	InputRange!string convention;

	this(T)(T range) if (isInputRange!T) {
		convention = inputRangeObject(range);
	}

	override void toPatternString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		this.toExprStringImpl(result, indent, context);
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		assert(this in context.names, "unassigned name: " ~ convention.front);
		result(context.names[this]);
	}

	override uint precedence() {
		return precedenceLiteral;
	}

	override JsContext updateContext(JsContext context) {
		return context.insert(this);
	}
}

abstract class JsState {
	void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context);
	override string toString() {
		string result;
		toStateString((const(char)[] str) { result ~= str; }, 0, JsContext());
		return result;
	}

	JsContext updateContext(JsContext context) {
		return context;
	}
}

abstract class JsLabel : JsState {
	string label;

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		if (label.length > 0) {
			result(label);
			result(":");
			line(result, indent);
		}
	}
}

class JsScope : JsLabel {
	JsState[] states;
	alias states this;

	this() {
	}

	this(JsState[] states) {
		this.states = states;
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		super.toStateString(result, indent, context);
		result("{");
		increase(indent);
		foreach (state; states) {
			line(result, indent);
			context = state.updateContext(context);
			state.toStateString(result, indent, context);
		}
		decrease(indent);
		line(result, indent);
		result("}");
	}
}

class JsImplictScope : JsScope {
	alias states this;
	this() {
	}

	this(JsState[] states) {
		super(states);
	}

	invariant() {
		assert(label == "");
	}
}

class JsIf : JsLabel {
	JsExpr cond;
	JsImplictScope yes;
	JsImplictScope no;
	this() {
		yes = new JsImplictScope();
		no = new JsImplictScope();
	}

	this(JsExpr cond, JsState[] yes, JsState[] no) {
		this.cond = cond;
		this.yes = new JsImplictScope(yes);
		this.no = new JsImplictScope(no);
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		super.toStateString(result, indent, context);
		result("if (");
		cond.toExprString(result, indent, context);
		result(") ");
		yes.toStateString(result, indent, context);
		if (no.length > 0) {
			result(" else ");
			no.toStateString(result, indent, context);
		}
	}
}

class JsWhile : JsLabel {
	JsExpr cond;
	JsImplictScope states;
	this() {
		states = new JsImplictScope();
	}

	this(JsExpr cond, JsState[] states) {
		this.cond = cond;
		this.states = new JsImplictScope(states);
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		super.toStateString(result, indent, context);
		result("while (");
		cond.toExprString(result, indent, context);
		result(")");
		states.toStateString(result, indent, context);
	}
}

class JsDoWhile : JsLabel {
	JsImplictScope states;
	JsExpr cond;
	this() {
		states = new JsImplictScope();
	}

	this(JsState[] states, JsExpr cond) {
		this.states = new JsImplictScope(states);
		this.cond = cond;
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		super.toStateString(result, indent, context);
		result("do ");
		states.toStateString(result, indent, context);
		result("while (");
		cond.toExprString(result, indent, context);
		result(");");
	}
}

class JsFor : JsLabel {
	JsVarDef vardef; //maybe null
	JsExpr cond; //maybe null
	JsExpr inc; //maybe null
	JsImplictScope states;
	this() {
		states = new JsImplictScope();
	}

	this(JsVarDef vardef, JsExpr cond, JsExpr inc, JsState[] states) {
		this.vardef = vardef;
		this.cond = cond;
		this.inc = inc;
		this.states = new JsImplictScope(states);
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		super.toStateString(result, indent, context);
		result("for (");
		if (vardef) {
			context = vardef.updateContext(context);
			vardef.toStateString(result, indent, context);
		} else {
			result(";");
		}
		if (cond) {
			cond.toExprString(result, indent, context);
		}
		result(";");
		if (inc) {
			inc.toExprString(result, indent, context);
		}
		result(")");
		states.toStateString(result, indent, context);
	}
}

interface JsPattern {
	void toPatternString(scope void delegate(const(char)[]) result, uint indent, JsContext context);
	JsContext updateContext(JsContext context);
}

class JsArrayPattern : JsPattern {
	JsPattern[] matches;
	this(JsPattern[] matches) {
		this.matches = matches;
	}

	void toPatternString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		result("[");
		foreach (c, match; matches) {
			match.toPatternString(result, indent, context);
			if (c != matches.length - 1) {
				result(", ");
			}
		}
		result("]");
	}

	JsContext updateContext(JsContext context) {
		return matches.fold!((context, match) => match.updateContext(context))(context);
	}
}

class JsVarDef : JsState {
	JsPattern pattern;
	JsExpr value; // nullable
	bool constant;

	this(JsPattern pattern, JsExpr value, bool constant) {
		this.pattern = pattern;
		this.value = value;
		this.constant = constant;
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		if (constant) {
			result("const ");
		} else {
			result("let ");
		}
		pattern.toPatternString(result, indent, context);
		if (value) {
			result(" = ");
			value.toExprString(result, indent, context);
		}
		result(";");
	}

	override JsContext updateContext(JsContext context) {
		return pattern.updateContext(context);
	}

}

class JsReturn : JsState {
	JsExpr expr; // maybe null
	this() {
	}

	this(JsExpr expr) {
		this.expr = expr;
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		result("return");
		if (expr) {
			result(" ");
			expr.toExprString(result, indent, context);
		}
		result(";");
	}
}

class JsContinue : JsState {
	string label;
	this() {
	}

	this(string label) {
		this.label = label;
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		result("continue");
		if (label.length > 0) {
			result(" ");
			result(label);
		}
		result(";");
	}
}

class JsBreak : JsState {
	string label;
	this() {
	}

	this(string label) {
		this.label = label;
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		result("break");
		if (label.length > 0) {
			result(" ");
			result(label);
		}
		result(";");
	}
}

// source: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Operator_Precedence

enum precedenceTable = ["=" : 3, "||" : 5, "&&" : 6, "|" : 8, "^" : 9, "&" : 10, "==" : 11, "!=" : 11, "===" : 11, "!==" : 11, ">" : 12, "<" : 12, ">=" : 12, "<=" : 12, "instanceof" : 12, "<<" : 13, ">>" : 13, ">>>" : 13, "+" : 14, "-" : 14, "*" : 15, "/" : 15, "%" : 15, "**" : 16];

enum precedencePrefix = 17;
enum precedencePostfix = 18;
enum precedenceCall = 20;
enum precedenceLiteral = 21;

abstract class JsExpr : JsState {
	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		toExprString(result, indent, context);
		result(";");
	}

	void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context);
	final void toExprString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		toExprString(result, indent, 0, context);
	}

	void toExprString(scope void delegate(const(char)[]) result, uint indent, uint precedence, JsContext context) {
		if (precedence > this.precedence) {
			result("(");
		}
		toExprStringImpl(result, indent, context);
		if (precedence > this.precedence) {
			result(")");
		}
	}

	uint precedence();
}

auto defaultNaming(string name) {
	name = name.replace(" ", "_");
	return chain(only(name), iota(0, uint.max).map!(a => name ~ a.to!string));
}

auto temporary() {
	return iota(0, uint.max).map!(a => "$" ~ a.to!string);
}

abstract class JsBasicLitImpl(JObject, Context = JsContext) : JObject {
	string value;

	this(string value) {
		this.value = value;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, Context context) {
		result(value);
	}

	override uint precedence() {
		return precedenceLiteral;
	}
}

alias JsBasicLit = JsBasicLitImpl!JsExpr;

class JsExternLit : JsBasicLit {
	this(string value) {
		super(value);
	}
}

class JsIntLitImpl(JObject, Context = JsContext) : JsBasicLitImpl!(JObject, Context) {
	this(long value) {
		super(value.to!string);
	}

	import std.bigint;

	this(BigInt value) {
		super(value.to!string);
	}
}

alias JsIntLit = JsIntLitImpl!JsExpr;

class JsDoubleLitImpl(JObject, Context = JsContext) : JsBasicLitImpl!(JObject, Context) {
	this(double value) {
		super(value.to!string);
	}
}

alias JsDoubleLit = JsDoubleLitImpl!JsExpr;

class JsBoolLitImpl(JObject, Context = JsContext) : JsBasicLitImpl!(JObject, Context) {
	this(bool value) {
		if (value) {
			super("true");
		} else {
			super("false");
		}
	}
}

alias JsBoolLit = JsBoolLitImpl!JsExpr;

string escape(dchar d) {
	if (d == '\0') {
		return "\\0"; //"\0" in js
	} else if (d == '\'') {
		return "'";
	} else if (d == '"') {
		return "\\\""; //"\"" in js
	}
	return d.to!string;
}

class JsCharLitImpl(JObject, Context = JsContext) : JsBasicLitImpl!(JObject, Context) {
	this(dchar value) {
		super('"' ~ escape(value) ~ '"');
	}

	this(string value) {
		super('"' ~ value.map!escape
				.joiner
				.to!string ~ '"');
	}
}

alias JsCharLit = JsCharLitImpl!JsExpr;

class JsThis : JsBasicLit {
	this() {
		super("this");
	}
}

class JsPrefix(string op) : JsExpr {
	JsExpr expr;
	this() {
	}

	this(JsExpr expr) {
		this.expr = expr;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		result(op);
		expr.toExprString(result, indent, precedence, context);
	}

	override uint precedence() {
		return precedencePrefix;
	}
}

class JsPostfix(string op) : JsExpr {
	JsExpr expr;
	this() {
	}

	this(JsExpr expr) {
		this.expr = expr;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		expr.toExprString(result, indent, precedence, context);
		result(op);
	}

	override uint precedence() {
		return precedencePostfix;
	}
}

class JsBinary(string op) : JsExpr {
	JsExpr left;
	JsExpr right;
	this() {
	}

	this(JsExpr left, JsExpr right) {
		this.left = left;
		this.right = right;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		left.toExprString(result, indent, precedence, context);
		result(" " ~ op ~ " ");
		right.toExprString(result, indent, precedence, context);
	}

	override uint precedence() {
		return precedenceTable[op];
	}
}

class JsCall : JsExpr {
	JsExpr func;
	JsExpr[] args;
	this() {
	}

	this(JsExpr func, JsExpr[] args) {
		this.func = func;
		this.args = args;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		func.toExprString(result, indent, precedence, context);
		result("(");
		foreach (c, arg; args) {
			arg.toExprString(result, indent, context);
			if (c != args.length - 1) {
				result(", ");
			}
		}
		result(")");
	}

	override uint precedence() {
		return precedencePostfix;
	}
}

class JsLambda : JsExpr {
	JsPattern[] arguments;
	JsImplictScope states;

	this(JsPattern[] arguments, JsState[] states) {
		this.arguments = arguments;
		this.states = new JsImplictScope(states);
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		foreach (argument; arguments) {
			context = argument.updateContext(context);
		}
		result("(");
		foreach (c, argument; arguments) {
			argument.toPatternString(result, indent, context);
			if (c != arguments.length - 1) {
				result(", ");
			}
		}
		result(") => ");
		states.toStateString(result, indent, context);
	}

	override uint precedence() {
		return 0;
	}
}

class JsArrayImpl(JObject, Context = JsContext) : JObject {
	JObject[] exprs;
	this() {
	}

	this(JObject[] exprs) {
		this.exprs = exprs;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, Context context) {
		result("[");
		foreach (c, expr; exprs) {
			expr.toExprString(result, indent, context);
			if (c != exprs.length - 1) {
				result(", ");
			}
		}
		result("]");
	}

	override uint precedence() {
		return precedenceLiteral;
	}
}

alias JsArray = JsArrayImpl!JsExpr;

class JsObjectImpl(JObject, Context = JsContext) : JObject {
	Tuple!(string, JObject)[] fields;
	this() {
	}

	this(Tuple!(string, JObject)[] fields) {
		this.fields = fields;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, Context context) {
		result("{");
		increase(indent);
		foreach (c, field; fields.enumerate) {
			line(result, indent);
			result(field[0]);
			result(" : ");
			field[1].toExprString(result, indent, context);
			if (c != fields.length - 1) {
				result(",");
			}
		}
		decrease(indent);
		line(result, indent);
		result("}");
	}

	override uint precedence() {
		return precedenceLiteral;
	}
}

alias JsObject = JsObjectImpl!JsExpr;

class JsDot : JsExpr {
	JsExpr object;
	string value;
	this() {
	}

	this(JsExpr object, string value) {
		this.object = object;
		this.value = value;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		object.toExprString(result, indent, precedence, context);
		result(".");
		result(value);
	}

	override uint precedence() {
		return precedenceCall;
	}
}

class JsIndex : JsExpr {
	JsExpr array;
	JsExpr index;
	this() {
	}

	this(JsExpr array, JsExpr index) {
		this.array = array;
		this.index = index;
	}

	override void toExprStringImpl(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		array.toExprString(result, indent, precedence, context);
		result("[");
		index.toExprString(result, indent, context);
		result("]");
	}

	override uint precedence() {
		return precedenceCall;
	}
}

class JsModule : JsImplictScope {
	alias states this;
	override void toStateString(scope void delegate(const(char)[]) result, uint indent, JsContext context) {
		foreach (state; states) {
			context = state.updateContext(context);
		}
		foreach (state; states) {
			state.toStateString(result, indent, context);
			result("\n");
		}
	}
}
