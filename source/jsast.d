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

abstract class JsState {
	void toStateString(scope void delegate(const(char)[]) result, uint indent);
	override string toString() {
		string result;
		toStateString((const(char)[] str) { result ~= str; }, 0);
		return result;
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

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
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

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		super.toStateString(result, indent);
		result("{");
		increase(indent);
		foreach (state; states) {
			line(result, indent);
			state.toStateString(result, indent);
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

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		super.toStateString(result, indent);
		result("if (");
		cond.toExprString(result, indent);
		result(")");
		yes.toStateString(result, indent);
		if (no.length > 0) {
			result(" else ");
			no.toStateString(result, indent);
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

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		super.toStateString(result, indent);
		result("while (");
		cond.toExprString(result, indent);
		result(")");
		states.toStateString(result, indent);
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

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		super.toStateString(result, indent);
		result("do ");
		states.toStateString(result, indent);
		result("while (");
		cond.toExprString(result, indent);
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

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		super.toStateString(result, indent);
		result("for (");
		if (vardef) {
			vardef.toStateString(result, indent);
		} else {
			result(";");
		}
		if (cond) {
			cond.toExprString(result, indent);
		}
		result(";");
		if (inc) {
			inc.toExprString(result, indent);
		}
		result(")");
		states.toStateString(result, indent);
	}
}

class JsVarDef : JsState {
	string name;
	JsExpr value;
	this() {
	}

	this(string name, JsExpr value) {
		this.name = name;
		this.value = value;
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		result("var ");
		result(name);
		result(" = ");
		value.toExprString(result, indent);
		result(";");
	}
}

class JsReturn : JsState {
	JsExpr expr; // maybe null
	this() {
	}

	this(JsExpr expr) {
		this.expr = expr;
	}

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		result("return");
		if (expr) {
			result(" ");
			expr.toExprString(result, indent);
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

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
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

	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
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
enum predHighest = predLit + 1;

abstract class JsExpr : JsState {
	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		toExprString(result, indent);
		result(";");
	}

	void toExprString(scope void delegate(const(char)[]) result, uint indent);
	void toExprString(scope void delegate(const(char)[]) result, uint indent, uint pred) {
		if (pred > this.pred) {
			result("(");
		}
		toExprString(result, indent);
		if (pred > this.pred) {
			result(")");
		}
	}

	uint pred();
}

//for int lits, bool lits, float lits and variables
class JsLit : JsExpr {
	string value;
	this() {
	}

	this(string value) {
		this.value = value;
	}

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		result(value);
	}

	override uint pred() {
		return predLit;
	}
}

class JsPrefix(string op) : JsExpr {
	JsExpr expr;
	this() {
	}

	this(JsExpr expr) {
		this.expr = expr;
	}

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		result(op);
		expr.toExprString(result, indent, pred);
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

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		expr.toExprString(result, indent, pred);
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

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		left.toExprString(result, indent, pred);
		result(" " ~ op ~ " ");
		right.toExprString(result, indent, pred);
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

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		func.toExprString(result, indent, pred);
		result("(");
		foreach (c, arg; args) {
			arg.toExprString(result, indent);
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
	string[] args;
	JsImplictScope states;
	this() {
		states = new JsImplictScope();
	}

	this(string[] args, JsState[] states) {
		this.args = args;
		this.states = new JsImplictScope(states);
	}

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		result("function (");
		foreach (c, arg; args) {
			result(arg);
			if (c != args.length - 1) {
				result(", ");
			}
		}
		result(")");
		states.toStateString(result, indent);
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

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		result("[");
		foreach (c, expr; exprs) {
			expr.toExprString(result, indent);
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

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		result("{");
		increase(indent);
		foreach (c, field; fields.enumerate) {
			line(result, indent);
			result(field[0]);
			result(" : ");
			field[1].toExprString(result, indent);
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

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		object.toExprString(result, indent, pred);
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

	override void toExprString(scope void delegate(const(char)[]) result, uint indent) {
		array.toExprString(result, indent, pred);
		result("[");
		index.toExprString(result, indent);
		result("]");
	}

	override uint pred() {
		return predPostfix;
	}
}

class JsModule : JsImplictScope {
	alias states this;
	override void toStateString(scope void delegate(const(char)[]) result, uint indent) {
		foreach (state; states) {
			state.toStateString(result, indent);
			result("\n");
		}
	}
}
