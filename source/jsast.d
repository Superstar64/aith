/+Copyright (C) 2016  Freddy Angel Cubas "Superstar64"

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, version 3 of the License.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
+/
import std.range;
import std.algorithm;
import std.typecons;

bool returns(JsState[] states) {
	return states.map!(a => a.returns).any;
}

abstract class JsState {
	bool returns() {
		return false;
	}

	void toStateString(ref string result, uint indent);
	override string toString() {
		string result;
		uint indent;
		toStateString(result, indent);
		return result;
	}

	static increase(ref uint indent) {
		indent += 4;
	}

	static decrease(ref uint indent) {
		indent -= 4;
	}

	static line(ref string result, uint indent) {
		result ~= "\n";
		foreach (_; 0 .. indent) {
			result ~= " ";
		}
	}
}

abstract class JsLabel : JsState {
	string label;

	override void toStateString(ref string result, uint indent) {
		if (label.length > 0) {
			result ~= label ~ ":";
			line(result, indent);
		}
	}
}

class JsScope : JsLabel {
	JsState[] states;
	this() {
	}

	this(JsState[] states) {
		this.states = states;
	}

	override bool returns() {
		return states.map!(a => a.returns).any;
	}

	override void toStateString(ref string result, uint indent) {
		super.toStateString(result, indent);
		result ~= "{";
		increase(indent);
		foreach (state; states) {
			line(result, indent);
			state.toStateString(result, indent);
		}
		decrease(indent);
		line(result, indent);
		result ~= "}";
	}
}

class JsIf : JsLabel {
	JsExpr cond;
	JsState[] yes;
	JsState[] no;
	this() {
	}

	this(JsExpr cond, JsState[] yes, JsState[] no) {
		this.cond = cond;
		this.yes = yes;
		this.no = no;
	}

	override bool returns() {
		return yes.map!(a => a.returns).any && no.map!(a => a.returns).any;
	}

	override void toStateString(ref string result, uint indent) {
		super.toStateString(result, indent);
		result ~= "if (";
		cond.toExprString(result, indent);
		result ~= ") {";
		increase(indent);
		foreach (state; yes) {
			line(result, indent);
			state.toStateString(result, indent);
		}
		decrease(indent);
		line(result, indent);
		result ~= "}";
		if (no.length > 0) {
			result ~= " else {";
			increase(indent);
			foreach (state; no) {
				line(result, indent);
				state.toStateString(result, indent);
			}
			decrease(indent);
			line(result, indent);
			result ~= "}";
		}
	}
}

class JsWhile : JsLabel {
	JsExpr cond;
	JsState[] states;
	this() {
	}

	this(JsExpr cond, JsState[] states) {
		this.cond = cond;
		this.states = states;
	}

	override void toStateString(ref string result, uint indent) {
		super.toStateString(result, indent);
		result ~= "while (";
		cond.toExprString(result, indent);
		result ~= ") {";
		increase(indent);
		foreach (state; states) {
			line(result, indent);
			state.toStateString(result, indent);
		}
		decrease(indent);
		line(result, indent);
		result ~= "}";
	}
}

class JsDoWhile : JsLabel {
	JsState[] states;
	JsExpr cond;
	this() {
	}

	this(JsState[] states, JsExpr cond) {
		this.states = states;
		this.cond = cond;
	}

	override void toStateString(ref string result, uint indent) {
		super.toStateString(result, indent);
		result ~= "do {";
		increase(indent);
		foreach (state; states) {
			line(result, indent);
			state.toStateString(result, indent);
		}
		decrease(indent);
		line(result, indent);
		result ~= "} while (";
		cond.toExprString(result, indent);
		result ~= ");";
	}
}

class JsFor : JsLabel {
	JsVarDef vardef; //maybe null
	JsExpr cond; //maybe null
	JsExpr inc; //maybe null
	JsState[] states;
	this() {
	}

	this(JsVarDef vardef, JsExpr cond, JsExpr inc, JsState[] states) {
		this.vardef = vardef;
		this.cond = cond;
		this.inc = inc;
		this.states = states;
	}

	override void toStateString(ref string result, uint indent) {
		super.toStateString(result, indent);
		result ~= "for (";
		if (vardef) {
			vardef.toStateString(result, indent);
		} else {
			result ~= ";";
		}
		if (cond) {
			cond.toExprString(result, indent);
		}
		result ~= ";";
		if (inc) {
			inc.toExprString(result, indent);
		}
		result ~= ") {";
		increase(indent);
		foreach (state; states) {
			line(result, indent);
			state.toStateString(result, indent);
		}
		decrease(indent);
		line(result, indent);
		result ~= "}";
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

	override void toStateString(ref string result, uint indent) {
		result ~= "var " ~ name ~ " = ";
		value.toExprString(result, indent);
		result ~= ";";
	}
}

class JsReturn : JsState {
	JsExpr expr; // maybe null
	this() {
	}

	this(JsExpr expr) {
		this.expr = expr;
	}

	override bool returns() {
		return true;
	}

	override void toStateString(ref string result, uint indent) {
		result ~= "return";
		if (expr) {
			result ~= " ";
			expr.toExprString(result, indent);
		}
		result ~= ";";
	}
}

class JsContinue : JsState {
	string label;
	this() {
	}

	this(string label) {
		this.label = label;
	}

	override void toStateString(ref string result, uint indent) {
		result ~= "continue";
		if (label.length > 0) {
			result ~= " ";
			result ~= label;
		}
		result ~= ";";
	}
}

class JsBreak : JsState {
	string label;
	this() {
	}

	this(string label) {
		this.label = label;
	}

	override void toStateString(ref string result, uint indent) {
		result ~= "break";
		if (label.length > 0) {
			result ~= " ";
			result ~= label;
		}
		result ~= ";";
	}
}

//dfmt off
enum precedence =
[["="], ["||"], ["&&"], ["|"], ["^"], ["&"],
 ["==", "!=", "===", "!=="], [">", "<", ">=", "<=", "instanceof"],
 ["<<", ">>", ">>>"], ["+", "-"], ["*", "/", "%"]];
//dfmt on
enum predPrefix = precedence.length + 1;
enum predPostfix = predPrefix + 1;
enum predLit = predPostfix + 1;
enum predHighest = predLit + 1;

abstract class JsExpr : JsState {
	override void toStateString(ref string result, uint indent) {
		toExprString(result, indent);
		result ~= ";";
	}

	void toExprString(ref string result, uint indent);
	void toExprString(ref string result, uint indent, uint pred) {
		if (pred > this.pred) {
			result ~= "(";
		}
		toExprString(result, indent);
		if (pred > this.pred) {
			result ~= ")";
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

	override void toExprString(ref string result, uint indent) {
		result ~= value;
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

	override void toExprString(ref string result, uint indent) {
		result ~= op;
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

	override void toExprString(ref string result, uint indent) {
		expr.toExprString(result, indent, pred);
		result ~= op;
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

	override void toExprString(ref string result, uint indent) {
		left.toExprString(result, indent, pred);
		result ~= " " ~ op ~ " ";
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

	override void toExprString(ref string result, uint indent) {
		func.toExprString(result, indent, pred);
		result ~= "(";
		foreach (c, arg; args) {
			arg.toExprString(result, indent);
			if (c != args.length - 1) {
				result ~= ", ";
			}
		}
		result ~= ")";
	}

	override uint pred() {
		return predPostfix;
	}
}

class JsFuncLit : JsExpr {
	string[] args;
	JsState[] states;
	this() {
	}

	this(string[] args, JsState[] states) {
		this.args = args;
		this.states = states;
	}

	override void toExprString(ref string result, uint indent) {
		result ~= "function (";
		foreach (c, arg; args) {
			result ~= arg;
			if (c != args.length - 1) {
				result ~= ", ";
			}
		}
		result ~= ") {";
		increase(indent);
		foreach (state; states) {
			line(result, indent);
			state.toStateString(result, indent);
		}
		decrease(indent);
		line(result, indent);
		result ~= "}";
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

	override void toExprString(ref string result, uint indent) {
		result ~= "[";
		foreach (c, expr; exprs) {
			expr.toExprString(result, indent);
			if (c != exprs.length - 1) {
				result ~= ", ";
			}
		}
		result ~= "]";
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

	override void toExprString(ref string result, uint indent) {
		result ~= "{";
		increase(indent);
		foreach (c, field; fields.enumerate) {
			line(result, indent);
			result ~= field[0] ~ " : ";
			field[1].toExprString(result, indent);
			if (c != fields.length - 1) {
				result ~= ",";
			}
		}
		decrease(indent);
		line(result, indent);
		result ~= "}";
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

	override void toExprString(ref string result, uint indent) {
		object.toExprString(result, indent, pred);
		result ~= "." ~ value;
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

	override void toExprString(ref string result, uint indent) {
		array.toExprString(result, indent, pred);
		result ~= "[";
		index.toExprString(result, indent);
		result ~= "]";
	}

	override uint pred() {
		return predPostfix;
	}
}

string stringCode(JsState[] states) {
	string result;
	uint indent;
	foreach (state; states) {
		state.toStateString(result, indent);
		JsState.line(result, indent);
	}
	return result;
}

unittest {
	import std.stdio;

	JsState[] ast = [
		new JsVarDef("myVar", new JsArray([new JsLit("0"), new JsLit("1")
	])),
		new JsWhile(new JsBinary!"<"(new JsLit("0"),
		new JsIndex(new JsLit("myVar"), new JsLit("1"))), [new JsPrefix!"--"(new JsLit("myVar"))])];
	writeln(ast.stringCode);
}
