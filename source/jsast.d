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
module jsast;

import std.algorithm;
import std.range;
import std.typecons;
import std.conv;

import std.range.interfaces;

struct JsContext {
	JsVariable[string] variables;
	string[JsVariable] names;
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

	static increase(ref uint indent) {
		indent += 4;
	}

	static decrease(ref uint indent) {
		indent -= 4;
	}

	static line(scope void delegate(const(char)[]) result, uint indent) {
		result("\n");
		foreach (_; 0 .. indent) {
			result(" ");
		}
	}
}

abstract class JsLabel : JsState {
	string label;

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
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

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
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

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		super.toStateString(result, indent, context);
		result("if (");
		cond.toExprString(result, indent, context);
		result(")");
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

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
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

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
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

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		super.toStateString(result, indent, context);
		result("for (");
		if (vardef) {
			context = vardef.variable.insert(context);
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

class JsVarDef : JsState {
	JsVariable variable;
	JsExpr value;

	this(JsVariable variable, JsExpr value) {
		this.variable = variable;
		this.value = value;
	}

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		result("var ");
		variable.toExprString(result, indent, context);
		result(" = ");
		value.toExprString(result, indent, context);
		result(";");
	}

	override JsContext updateContext(JsContext context) {
		return variable.insert(context);
	}

}

class JsReturn : JsState {
	JsExpr expr; // maybe null
	this() {
	}

	this(JsExpr expr) {
		this.expr = expr;
	}

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
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

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
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

	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		result("break");
		if (label.length > 0) {
			result(" ");
			result(label);
		}
		result(";");
	}
}

enum precedence = [
		["="], ["||"], ["&&"], ["|"], ["^"], ["&"], ["==", "!=", "===", "!=="],
		[">", "<", ">=", "<=", "instanceof"], ["<<", ">>", ">>>"], ["+", "-"],
		["*", "/", "%"]
	];

enum predPrefix = precedence.length + 1;
enum predPostfix = predPrefix + 1;
enum predLit = predPostfix + 1;

abstract class JsExpr : JsState {
	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		toExprString(result, indent, context);
		result(";");
	}

	void toExprString(scope void delegate(const(char)[]) result, uint indent, JsContext context);
	void toExprString(scope void delegate(const(char)[]) result, uint indent,
			uint pred, JsContext context) {
		if (pred > this.pred) {
			result("(");
		}
		toExprString(result, indent, context);
		if (pred > this.pred) {
			result(")");
		}
	}

	uint pred();
}

auto defaultNaming(string name) {
	name = name.replace(" ", "_");
	return chain(only(name), iota(0, uint.max).map!(a => name ~ a.to!string));
}

auto temporary() {
	return iota(0, uint.max).map!(a => "$" ~ a.to!string);
}

class JsVariable : JsExpr {
	InputRange!string convention;

	this(T)(T range) if (isInputRange!T) {
		convention = inputRangeObject(range);
	}

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		assert(this in context.names, "unassigned name: " ~ convention.front);
		result(context.names[this]);
	}

	override uint pred() {
		return predLit;
	}

	final JsContext insert(JsContext context) {
		foreach (name; convention) {
			if (!(name in context.variables)) {
				context.variables[name] = this;
				context.names[this] = name;
				return context;
			}
		}
		assert(0);
	}
}

abstract class JsBasicLit : JsExpr {
	string value;

	this(string value) {
		this.value = value;
	}

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		result(value);
	}

	override uint pred() {
		return predLit;
	}
}

class JsExternLit : JsBasicLit {
	this(string name) {
		super(name);
	}
}

class JsIntLit : JsBasicLit {
	this(long value) {
		super(value.to!string);
	}
}

class JsDoubleLit : JsBasicLit {
	this(double value) {
		super(value.to!string);
	}
}

class JsBoolLit : JsBasicLit {
	this(bool value) {
		if (value) {
			super("true");
		} else {
			super("false");
		}
	}
}

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

class JsCharLit : JsBasicLit {
	this(dchar value) {
		super('"' ~ escape(value) ~ '"');
	}
}

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

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		result(op);
		expr.toExprString(result, indent, pred, context);
	}

	override uint pred() {
		return predPrefix;
	}
}

class JsPostfix(string op) : JsExpr {
	JsExpr expr;
	this() {
	}

	this(JsExpr expr) {
		this.expr = expr;
	}

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		expr.toExprString(result, indent, pred, context);
		result(op);
	}

	override uint pred() {
		return predPostfix;
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

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		left.toExprString(result, indent, pred, context);
		result(" " ~ op ~ " ");
		right.toExprString(result, indent, pred, context);
	}

	override uint pred() {
		return cast(uint) precedence.enumerate.filter!(a => a[1].canFind(op)).front[0];
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

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		func.toExprString(result, indent, pred, context);
		result("(");
		foreach (c, arg; args) {
			arg.toExprString(result, indent, context);
			if (c != args.length - 1) {
				result(", ");
			}
		}
		result(")");
	}

	override uint pred() {
		return predPostfix;
	}
}

class JsFuncLit : JsExpr {
	JsVariable[] args;
	JsImplictScope states;

	this(JsVariable[] args, JsState[] states) {
		this.args = args;
		this.states = new JsImplictScope(states);
	}

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		foreach (arg; args) {
			context = arg.insert(context);
		}
		result("function (");
		foreach (c, arg; args) {
			context = arg.insert(context);
			arg.toExprString(result, indent, context);
			if (c != args.length - 1) {
				result(", ");
			}
		}
		result(")");
		states.toStateString(result, indent, context);
	}

	override uint pred() {
		return predLit;
	}
}

class JsArray : JsExpr {
	JsExpr[] exprs;
	this() {
	}

	this(JsExpr[] exprs) {
		this.exprs = exprs;
	}

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		result("[");
		foreach (c, expr; exprs) {
			expr.toExprString(result, indent, context);
			if (c != exprs.length - 1) {
				result(", ");
			}
		}
		result("]");
	}

	override uint pred() {
		return predLit;
	}
}

class JsObject : JsExpr {
	Tuple!(string, JsExpr)[] fields;
	this() {
	}

	this(Tuple!(string, JsExpr)[] fields) {
		this.fields = fields;
	}

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
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

	override uint pred() {
		return predLit;
	}
}

class JsDot : JsExpr {
	JsExpr object;
	string value;
	this() {
	}

	this(JsExpr object, string value) {
		this.object = object;
		this.value = value;
	}

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		object.toExprString(result, indent, pred, context);
		result(".");
		result(value);
	}

	override uint pred() {
		return predPostfix;
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

	override void toExprString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		array.toExprString(result, indent, pred, context);
		result("[");
		index.toExprString(result, indent, context);
		result("]");
	}

	override uint pred() {
		return predPostfix;
	}
}

class JsModule : JsImplictScope {
	alias states this;
	override void toStateString(scope void delegate(const(char)[]) result,
			uint indent, JsContext context) {
		foreach (state; states) {
			context = state.updateContext(context);
		}
		foreach (state; states) {
			state.toStateString(result, indent, context);
			result("\n");
		}
	}
}
