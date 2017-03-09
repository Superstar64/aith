/+
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
module ast;

import std.bigint : BigInt;
import std.traits : isArray;
import std.variant : Algebraic;
import lexer : Position;

alias Index = Algebraic!(BigInt, string);
alias visiter = int delegate(Node, Trace);

int visitChildren(T)(ref T child, visiter fun, Trace trace) if (is(T : Node)) {
	return fun(child, trace);
}

int visitChildren(T)(ref T children, visiter fun, Trace trace) if (isArray!T) {
	foreach (ref child; children) {
		int result = visitChildren(child, fun, trace);
		if (result) {
			return result;
		}
	}
	return 0;
}

mixin template autoChildren(T...) {
	override int children_(visiter fun, Trace trace) {
		foreach (ref child; T) {
			int result = super.children_(fun, trace);
			if (result) {
				return result;
			}
			result = visitChildren(child, fun, trace);
			if (result) {
				return result;
			}
		}
		return 0;
	}
}

abstract class Trace {
	Trace upper;
	Module[] imports;
	Module[][string[]] staticimports;
	Type[string] aliases;
	abstract Var getVar(string);
	final Var var(string name, string[] namespace) {
		Trace t;
		return var(name, namespace, t);
	}

	final Var var(string name, string[] namespace, out Trace t) {

		if (namespace is null) {
			auto v = getVar(name);
			if (v) {
				t = this;
				return v;
			}
			foreach (m; imports) {
				if (name in m.vars) {
					t = m.genTrace(null);
					return m.vars[name];
				}
			}
		} else {
			if (namespace in staticimports) {
				auto mods = staticimports[namespace];
				foreach (m; mods) {
					if (name in m.vars) {
						t = m.genTrace(null);
						return m.vars[name];
					}
				}
			}
		}
		if (upper) {
			return upper.var(name, namespace, t);
		} else {
			return null;
		}
	}

	final Type type(string name, string[] namespace) {
		if (namespace is null) {
			auto v = name in aliases;
			if (v) {
				return *v;
			}
			foreach (m; imports) {
				if (name in m.aliases) {
					return m.aliases[name];
				}
			}
		} else {
			if (namespace in staticimports) {
				auto mods = staticimports[namespace];
				foreach (m; mods) {
					if (name in m.aliases) {
						return m.aliases[name];
					}
				}
			}
		}
		if (upper) {
			return upper.type(name, namespace);
		} else {
			return null;
		}
	}
}

abstract class Node { //base class for all ast nodes
	Position pos;

	final auto children(Trace t) {
		static struct Looper {
			Node n;
			Trace trace;
			int opApply(visiter fn) {
				return n.children_(fn, trace);
			}
		}

		return Looper(this, t);
	}

	int children_(visiter, Trace) {
		return 0;
	}
}

abstract class Var : Node {
	string name;
	bool manifest;
	bool heap; //has the address of the variable been taken,does not apply to closures
	@property abstract ref Type getType();
}

class ModuleVar : Var {
	Value def;
	bool process;
	@property override ref Type getType() {
		return def.type;
	}

	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(def, t);
		return res;
	}
}

class Module : Node {
	Type[string] aliases;
	Module[] imports;
	Module[][string[]] staticimports;
	ModuleVar[string] vars;
	string[] namespace;
	static class ModuleTrace : Trace {
		private this(Module mod) {
			imports = mod.imports;
			staticimports = mod.staticimports;
			aliases = mod.aliases;
			m = mod;
		}

		Module m;
		override Var getVar(string s) {
			if (s in m.vars) {
				return m.vars[s];
			}
			return null;
		}
	}

	ModuleTrace genTrace(Trace t) {
		return new ModuleTrace(this);
	}

	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		auto subt = genTrace(t);
		foreach (ty; aliases) {
			res = fn(ty, subt);
			if (res) {
				return res;
			}
		}
		foreach (v; vars) {
			res = fn(v, subt);
			if (res) {
				return res;
			}
		}
		return res;
	}
}

/+
 + Types 
 +/

abstract class Type : Node {
	@property Type actual() {
		return this;
	}
}

class Bool : Type {

}

class Char : Type {
}

class Int : Type {
	this(uint _) {
		size = _;
	}

	uint size;
}

class UInt : Type {
	this(uint _) {
		size = _;
	}

	uint size;
}

class Struct : Type {
	Type[] types;
	size_t[string] names;
	mixin autoChildren!types;
}

class Pointer : Type {
	Type type;
	mixin autoChildren!type;
}

class Array : Type {
	Type type;
	mixin autoChildren!type;
}

class Function : Type {
	Type ret;
	Type arg;
	bool ispure;
	mixin autoChildren!(ret, arg);
}

abstract class IndirectType : Type {
	Type actual_;
	@property override Type actual() {
		return actual_.actual;
	}
}

class SubType : IndirectType {
	Type type;
	mixin autoChildren!type;
}

class IndexType : IndirectType {
	Type type;
	Index index;
	mixin autoChildren!type;
}

class UnknownType : IndirectType {
	string name;
	string[] namespace;
}

/+
 + Values
 +/

abstract class Value : Node {
	Type type;
	bool lvalue;
	bool ispure;
}

class IntLit : Value {
	BigInt value;
	bool usigned;
}

class CharLit : Value {
	dchar value;
}

class BoolLit : Value {
	bool yes;
}

class StructLit : Value {
	Value[] values;
	size_t[string] names;
	mixin autoChildren!values;
}

class Variable : Value {
	string name;
	string[] namespace;
}

class If : Value {
	Value cond;
	Value yes;
	Value no;
	mixin autoChildren!(cond, yes, no);
}

class While : Value {
	Value cond;
	Value state;
	mixin autoChildren!(cond, state);
}

class New : Value {
	Value value;
	mixin autoChildren!value;
}

class NewArray : Value {
	Value length;
	Value value;
	mixin autoChildren!(length, value);
}

class Cast : Value {
	Value value;
	Type wanted;
	mixin autoChildren!(value, wanted);
}

class Dot : Value {
	Value value;
	Index index;
	mixin autoChildren!value;
}

class ArrayIndex : Value {
	Value array;
	Value index;
	mixin autoChildren!(array, index);
}

class FCall : Value {
	Value fptr;
	Value arg;
	mixin autoChildren!(fptr, arg);
}

class Slice : Value {
	Value array;
	Value left;
	Value right;
	mixin autoChildren!(array, left, right);
}

/+
	"*","/","%",
	"+","-","~",
	"&","|","^","<<",">>",">>>",
	"==","!=","<=",">=","<",">",
	"&&","||",
	"="
 +/
class Binary(string T) : Value {
	Value left;
	Value right;
	mixin autoChildren!(left, right);
}

/+
	"+","-","*","/","&","~","!"
+/
class Prefix(string T) : Value {
	Value value;
	mixin autoChildren!value;
}
//for position dependant statementss
alias Statement = Algebraic!(Value, ScopeVar);

class ScopeVar : Var {
	Value def;
	@property override ref Type getType() {
		return def.type;
	}

	mixin autoChildren!def;
}

class Scope : Value {
	Type[string] aliases;
	Module[] imports;
	Module[][string[]] staticimports;
	Statement[] states;
	bool noreturn;
	static class ScopeTrace : Trace {
		Scope scop;
		ScopeVar[string] vars;
		private this(Scope sc, Trace upper_) {
			scop = sc;
			imports = sc.imports;
			staticimports = sc.staticimports;
			aliases = sc.aliases;
			upper = upper_;
		}

		override Var getVar(string n) {
			if (n in vars) {
				return vars[n];
			}
			return null;
		}
	}

	ScopeTrace genTrace(Trace t) {
		return new ScopeTrace(this, t);
	}

	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		auto subt = genTrace(t);

		foreach (ty; aliases) {
			res = fn(ty, subt);
			if (res) {
				return res;
			}
		}
		foreach (s; states) {
			if (s.peek!Value) {
				res = fn(s.get!Value, subt);
			} else {
				res = fn(s.get!ScopeVar, subt);
				subt.vars[s.get!(ScopeVar).name] = s.get!ScopeVar;
			}
			if (res) {
				return res;
			}
		}

		return res;
	}
}

class FuncLitVar : Var {
	Type ty;
	override ref Type getType() {
		return ty;
	}

	mixin autoChildren!ty;
}

class FuncLit : Value {
	FuncLitVar fvar;
	Value text;
	Type explict_return; //maybe null
	static class FuncLitTrace : Trace {
		FuncLit func;
		private this(FuncLit f, Trace upper_) {
			upper = upper_;
			func = f;
		}

		override Var getVar(string s) {
			if (func.fvar.name == s) {
				return func.fvar;
			}
			return null;
		}
	}

	FuncLitTrace genTrace(Trace t) {
		return new FuncLitTrace(this, t);
	}

	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		auto subt = genTrace(t);
		res = fn(fvar, subt);
		if (res) {
			return res;
		}
		res = fn(text, subt);
		return res;
	}
}

class Return : Value {
	Value value;
	uint upper = uint.max;
	mixin autoChildren!value;
}

class StringLit : Value {
	string str;
}

class ArrayLit : Value {
	Value[] values;
	mixin autoChildren!values;
}

class ExternJS : Value {
	Type type;
	string external;
	mixin autoChildren!type;
}
