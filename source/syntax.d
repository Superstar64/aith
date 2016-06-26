/+Copyright (C) 2015  Freddy Angel Cubas "Superstar64"

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
module syntax;
import std.bigint : BigInt;
import std.variant : Algebraic;
import std.utf : decodeFront;
import error : error;
import lexer;
import etc;

//todo support chars and immutable types
@trusted:
alias Index = Algebraic!(BigInt, string);
alias visiter = int delegate(Node, Trace);

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
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		foreach (ty; types) {
			res = fn(ty, t);
			if (res) {
				return res;
			}
		}
		return res;
	}
}

class Pointer : Type {
	Type type;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(type, t);
		return res;
	}
}

class Array : Type {
	Type type;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(type, t);
		return res;
	}
}

class Function : Type {
	Type ret;
	Type arg;
	bool ispure;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(ret, t);
		if (res) {
			return res;
		}
		res = fn(arg, t);
		return res;
	}
}

abstract class IndirectType : Type {
	Type actual_;
	@property override Type actual() {
		return actual_.actual;
	}
}

class SubType : IndirectType {
	Type type;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(type, t);
		return res;
	}
}

class IndexType : IndirectType {
	Type type;
	Index index;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(type, t);
		return res;
	}
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
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		foreach (v; values) {
			res = fn(v, t);
			if (res) {
				return res;
			}
		}
		return res;
	}
}

class Variable : Value {
	string name;
	string[] namespace;
}

class If : Value {
	Value cond;
	Value yes;
	Value no;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(cond, t);
		if (res) {
			return res;
		}
		res = fn(yes, t);
		if (res) {
			return res;
		}
		res = fn(no, t);
		return res;
	}
}

class While : Value {
	Value cond;
	Value state;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(cond, t);
		if (res) {
			return res;
		}
		res = fn(state, t);
		return res;
	}
}

class New : Value {
	Value value;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(value, t);
		return res;
	}
}

class NewArray : Value {
	Value length;
	Value value;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(length, t);
		if (res) {
			return res;
		}
		res = fn(value, t);
		return res;
	}
}

class Cast : Value {
	Value value;
	Type wanted;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(value, t);
		if (res) {
			return res;
		}
		res = fn(wanted, t);
		return res;
	}
}

class Dot : Value {
	Value value;
	Index index;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(value, t);
		return res;
	}
}

class ArrayIndex : Value {
	Value array;
	Value index;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(array, t);
		if (res) {
			return res;
		}
		res = fn(index, t);
		return res;
	}
}

class FCall : Value {
	Value fptr;
	Value arg;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(fptr, t);
		if (res) {
			return res;
		}
		res = fn(arg, t);
		return res;
	}
}

class Slice : Value {
	Value array;
	Value left;
	Value right;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(array, t);
		if (res) {
			return res;
		}
		res = fn(left, t);
		if (res) {
			return res;
		}
		res = fn(right, t);
		return res;
	}
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
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(left, t);
		if (res) {
			return res;
		}
		res = fn(right, t);
		return res;
	}
}

/+
	"+","-","*","/","&","~","!"
+/
class Prefix(string T) : Value {
	Value value;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(value, t);
		return res;
	}
}
//for position dependant statementss
alias Statement = Algebraic!(Value, ScopeVar);

class ScopeVar : Var {
	Value def;
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

	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(ty, t);
		return res;
	}
}

class FuncLit : Value {
	FuncLitVar fvar;
	Value text;
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
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(value, t);
		return res;
	}
}

class StringLit : Value {
	string str;
}

class ArrayLit : Value {
	Value[] values;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		foreach (v; values) {
			res = fn(v, t);
			if (res) {
				return res;
			}
		}
		return res;
	}
}

class ExternJS : Value {
	Type type;
	string external;
	override int children_(visiter fn, Trace t) {
		int res;
		res = super.children_(fn, t);
		if (res) {
			return res;
		}
		res = fn(type, t);
		return res;
	}
}

struct Parser {
	Lexer l;
	Module delegate(string[]) onImport;

	/++
	 + Types
	 +/

	Type parseType(bool nullable = false) {
		Type ty;
		ty = parseTypeBasic;
		if (ty) {
			goto end;
		}

		ty = parseTypeFunc;
		if (ty) {
			goto end;
		}

		ty = parseTypeStruct;
		if (ty) {
			goto end;
		}

		ty = parseTypeUnknown;
		if (ty) {
			goto end;
		}

		ty = parseTypeSub;
		if (ty) {
			goto end;
		}

		if (nullable) {
			return null;
		} else {
			error("Expected Type", l.front.pos);
			assert(0);
		}

	end:
		ty = parseTypePostfix(ty);
		return ty;
	}

	Type parseTypeBasic() {
		uint parseDotFix() {
			if (l.front == oper!".") {
				l.popFront;
				uint res = toUInt(l.front.expectT!(IntLiteral));
				l.popFront;
				return res;
			}
			return 0;
		}

		Type ret;
		auto pos = l.front.pos;
		scope (exit) {
			if (ret) {
				ret.pos = pos.join(l.front.pos);
			}
		}
		if (l.front == key!"int_t") {
			l.popFront;
			ret = new Int(parseDotFix);
		} else if (l.front == key!"uint_t") {
			l.popFront;
			ret = new UInt(parseDotFix);
		} else if (l.front == key!"char") {
			l.popFront;
			ret = new Char();
		} else if (l.front == key!"bool_t") {
			l.popFront;
			ret = new Bool();
		}
		return ret;
	}

	Type parseTypePostfix(Type current) {
		auto pos = current.pos;
		if (l.front == oper!"*") {
			auto ret = new Pointer();
			l.popFront;
			ret.type = current;
			ret.pos = pos.join(l.front.pos);
			return parseTypePostfix(ret);
		} else if (l.front == oper!"[") {
			auto ret = new Array();
			l.popFront;
			l.front.expect(oper!"]");
			l.popFront;
			ret.type = current;
			ret.pos = pos.join(l.front.pos);
			return parseTypePostfix(ret);
		} else if (l.front == oper!".") {
			auto ret = new IndexType();
			l.popFront;
			l.front.expectT!(Identifier, IntLiteral);
			if (l.front.peek!Identifier) {
				ret.index = l.front.get!(Identifier).name;
			} else {
				ret.index = l.front.get!(IntLiteral).num;
			}
			l.popFront;
			ret.type = current;
			ret.pos = pos.join(l.front.pos);
			return parseTypePostfix(ret);
		}
		return current;
	}

	Type parseTypeFunc() {
		if (l.front == oper!"$") {
			auto ret = new Function();
			auto pos = l.front.pos;
			scope (exit) {
				ret.pos = pos.join(l.front.pos);
			}
			l.popFront;
			ret.ret = parseType();
			l.front.expect(oper!":");
			l.popFront;
			ret.arg = parseType();
			return ret;
		}
		return null;
	}

	Type parseTypeStruct() {
		if (l.front == oper!"{") {
			auto ret = new Struct();
			auto pos = l.front.pos;
			scope (exit) {
				ret.pos = pos.join(l.front.pos);
			}
			l.popFront;
			if (l.front != oper!"}") {
				uint count;
				while (true) {
					ret.types ~= parseType();
					if (l.front.peek!Identifier) {
						ret.names[l.front.get!(Identifier).name] = count;
						l.popFront;
					}
					if (l.front != oper!",") {
						break;
					}
					l.popFront;
					count++;
				}
				l.front.expect(oper!"}");
			}
			l.popFront;
			if (ret.types.length == 1 && ret.names.length == 0) {
				return ret.types[0];
			}
			return ret;
		}
		return null;
	}

	Type parseTypeUnknown() {
		if (l.front.peek!Identifier) {
			auto ret = new UnknownType();
			auto pos = l.front.pos;
			scope (exit) {
				ret.pos = pos.join(l.front.pos);
			}
			while (true) {
				l.front.expectT!Identifier;
				ret.name = l.front.get!(Identifier).name;
				l.popFront;
				if (l.front != oper!"::") {
					break;
				}
				ret.namespace ~= ret.name;
				l.popFront;
			}
			return ret;
		}
		return null;
	}

	Type parseTypeSub() {
		if (l.front == oper!"*") {
			auto ret = new SubType();
			auto pos = l.front.pos;
			scope (exit) {
				ret.pos = pos.join(l.front.pos);
			}
			l.popFront;
			ret.type = parseType;
			return ret;
		}
		return null;
	}

	Value parseValue(bool nullable = false) {
		return parseBinary!("=", parseBinary!("&&", "||", parseBinary!("==",
			"!=", "<=", ">=", "<", ">", parseBinary!("&", "|", "^", "<<",
			">>", ">>>", parseBinary!("+", "-", "~", parseBinary!("*", "/",
			"%", parseValuePrefix!("+", "-", "*", "/", "&", "~", "!")))))));
	}

	Value parseBinary(args...)() {
		alias opers = args[0 .. $ - 1];
		alias sub = args[$ - 1];
		auto pos = l.front.pos;
		auto val = sub;
		foreach (o; opers) {
			if (l.front == oper!o) {
				auto ret = new Binary!o;
				l.popFront;
				ret.left = val;
				ret.right = parseBinary!args;
				ret.pos = pos.join(l.front.pos);
				return ret;
			}
		}
		return val;
	}

	Value parseValuePrefix(opers...)() {
		auto pos = l.front.pos;
		foreach (o; opers) {
			if (l.front == oper!o) {
				static if (o == "+" || o == "-") { //hacky special case
					auto old = l;
					bool usign = l.front == oper!"+";
					bool nega = l.front == oper!"-";
					l.popFront;
					auto intL = parseValueIntLit(usign, nega);
					if (intL) {
						intL.pos = pos.join(l.front.pos);
						return parseValuePostfix(intL);
					}
					l = old;
				}
				auto ret = new Prefix!o;
				l.popFront;
				ret.value = parseValuePrefix!(opers);
				ret.pos = pos.join(l.front.pos);
				return ret;
			}
		}
		return parseValueCore;
	}
	/++
	 + Values
	 +/

	Value parseValueCore(bool nullable = false) {
		Value val;
		val = parseValueBasic;
		if (val) {
			goto end;
		}

		val = parseValueStruct!(oper!"(", oper!")");
		if (val) {
			goto end;
		}

		val = parseValueVar;
		if (val) {
			goto end;
		}

		val = parseValueIf;
		if (val) {
			goto end;
		}

		val = parseValueWhile;
		if (val) {
			goto end;
		}

		val = parseValueNew;
		if (val) {
			goto end;
		}

		val = parseValueScope;
		if (val) {
			goto end;
		}

		val = parseValueFuncLit;
		if (val) {
			goto end;
		}

		val = parseValueReturn;
		if (val) {
			goto end;
		}

		val = parseStringLit;
		if (val) {
			goto end;
		}

		val = parseArrayLit;
		if (val) {
			goto end;
		}

		val = parseExtern;
		if (val) {
			goto end;
		}

		if (nullable) {
			return null;
		} else {
			error("Expected Value", l.front.pos);
			return null;
		}

	end:
		val = parseValuePostfix(val);
		return val;
	}

	Value parseValueBasic() {
		auto pos = l.front.pos;
		auto intL = parseValueIntLit;
		if (intL) {
			intL.pos = pos.join(l.front.pos);
			return intL;
		} else if (l.front == key!"true") {
			auto ret = new BoolLit();
			ret.yes = true;
			l.popFront;
			ret.pos = pos.join(l.front.pos);
			return ret;
		} else if (l.front == key!"false") {
			auto ret = new BoolLit();
			ret.yes = false;
			l.popFront;
			ret.pos = pos.join(l.front.pos);
			return ret;
		} else if (l.front.peek!CharLiteral) {
			auto ret = new CharLit();
			auto str = l.front.get!(CharLiteral).data;
			ret.value = decodeFront(str);
			if (str.length != 0) {
				error("Char Lit to big", l.front.pos);
			}
			l.popFront;
			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Value parseValueIntLit(bool posi = false, bool nega = false) {
		if (l.front.peek!IntLiteral) {
			auto ret = new IntLit;
			ret.value = l.front.get!(IntLiteral).num;
			ret.usigned = posi;
			if (nega) {
				ret.value = -ret.value;
			}
			l.popFront;
			return ret;
		}
		return null;
	}

	Value parseValueStructimp() {
		auto ret = new StructLit();
		while (true) {
			ret.values ~= parseValue();
			if (l.front != oper!",") {
				break;
			}
			l.popFront;
		}
		if (ret.values.length == 1 && ret.names.length == 0) {
			return ret.values[0];
		}
		return ret;
	}

	Value parseValueStruct(alias Front = oper!"(", alias End = oper!")")() {
		Value val;
		auto pos = l.front.pos;
		if (l.front == Front) {
			l.popFront;
			if (l.front == End) {
				l.popFront;
				return new StructLit();
			}
			val = parseValueStructimp;
			l.front.expect(End);
			l.popFront;
			val.pos = pos.join(l.front.pos);
		}
		return val;
	}

	Value parseValueVar() {
		auto pos = l.front.pos;
		if (l.front.peek!Identifier) {
			auto ret = new Variable();
			while (true) {
				ret.name = l.front.get!(Identifier).name;
				l.popFront;
				if (l.front != oper!"::") {
					break;
				}
				l.popFront;
				ret.namespace ~= ret.name;
			}
			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Value parseValueIf() {
		auto pos = l.front.pos;
		if (l.front == key!"if") {
			auto ret = new If();
			l.popFront;
			ret.cond = parseValue;
			l.front.expect(key!"then");
			l.popFront;
			ret.yes = parseValue;
			if (l.front == key!"else") {
				l.popFront;
				ret.no = parseValue;
			} else {
				ret.no = new StructLit();
			}
			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Value parseValueWhile() {
		auto pos = l.front.pos;
		if (l.front == key!"while") {
			auto ret = new While();
			l.popFront;
			ret.cond = parseValue;
			if (l.front == key!"then") {
				l.popFront;
				ret.state = parseValue;
			} else {
				ret.state = new StructLit();
			}
			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Value parseValueNew() {
		auto pos = l.front.pos;
		if (l.front == key!"new") {
			l.popFront;
			if (l.front == oper!"[") {
				auto ret = new NewArray();
				ret.length = parseValueStruct!(oper!"[", oper!"]");
				assert(ret.length);
				ret.value = parseValue;
				ret.pos = pos.join(l.front.pos);
				return ret;
			} else {
				auto ret = new New();
				ret.value = parseValue;
				ret.pos = pos.join(l.front.pos);
				return ret;
			}
		}
		return null;
	}

	Value parseValuePostfix(Value current) {
		auto pos = current.pos;
		if (l.front == oper!":") {
			auto ret = new Cast();
			ret.value = current;
			l.popFront;
			ret.wanted = parseType;
			if (!(l.front == oper!";" || l.front == oper!"}" || l.front == oper!")")) {
				l.front.expect(oper!":");
				l.popFront;
			}
			ret.pos = pos.join(l.front.pos);
			return parseValuePostfix(ret);
		} else if (l.front == oper!".") {
			auto ret = new Dot();
			ret.value = current;
			l.popFront;
			l.front.expectT!(IntLiteral, Identifier);
			if (l.front.peek!Identifier) {
				ret.index = l.front.get!(Identifier).name;
			} else {
				ret.index = l.front.get!(IntLiteral).num;
			}
			l.popFront;
			ret.pos = pos.join(l.front.pos);
			return parseValuePostfix(ret);
		} else if (l.front == oper!"[") {
			auto pos2 = l.front.pos;
			l.popFront;
			if (l.front == oper!"]") {
				l.popFront;
				auto ret = new ArrayIndex;
				ret.array = current;
				ret.index = new StructLit();
				ret.index.pos = pos2.join(l.front.pos);
				ret.pos = pos.join(l.front.pos);
				return parseValuePostfix(ret);
			}
			auto val = parseValueStructimp;
			if (l.front == oper!"..") {
				auto ret = new Slice;
				ret.array = current;
				ret.left = val;
				ret.left.pos = pos2.join(l.front.pos);

				l.popFront;
				pos2 = l.front.pos;

				ret.right = parseValueStructimp;
				l.front.expect(oper!"]");
				l.popFront;
				ret.right.pos = pos2.join(l.front.pos);
				ret.pos = pos.join(l.front.pos);
				return parseValuePostfix(ret);
			} else {
				assert(l.front == oper!"]");
				l.popFront;
				auto ret = new ArrayIndex;
				ret.array = current;
				ret.index = val;
				ret.index.pos = pos2.join(l.front.pos);
				ret.pos = pos.join(l.front.pos);
				return parseValuePostfix(ret);
			}
		} else {
			auto tmp = parseValueCore(true);
			if (tmp) {
				auto ret = new FCall();
				ret.fptr = current;
				ret.arg = tmp;
				ret.pos = pos.join(l.front.pos);
				return parseValuePostfix(ret);
			}
		}
		return current;
	}

	Value parseValueScope() {
		auto pos = l.front.pos;
		if (l.front == oper!"{") {
			l.popFront;
			auto ret = parseValueScopeimp!(oper!"}")();
			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Value parseValueScopeimp(alias end = oper!"}")() {
		auto ret = new Scope();
		while (true) {
			if (l.front == end) {
				l.popFront;
				return ret;
			}
			if (l.front == key!"import") {
				l.popFront;
				string[] namespace;
				while (l.front.expectT!(Identifier)) {
					namespace ~= l.front.get!(Identifier).name;
					l.popFront;
					if (l.front == oper!"::") {
						l.popFront;
						continue;
					}
					break;
				}
				if (l.front == oper!"=") {
					l.popFront;
					string[] name;
					name = namespace;
					namespace = null;
					while (l.front.expectT!(Identifier)) {
						namespace ~= l.front.get!(Identifier).name;
						l.popFront;
						if (l.front == oper!"::") {
							l.popFront;
							continue;
						}
						break;
					}
					ret.staticimports[name.idup] ~= onImport(namespace);
				} else {
					ret.imports ~= onImport(namespace);
				}

			} else if (l.front == key!"alias") {
				l.popFront;
				l.front.expectT!Identifier;
				auto name = l.front.get!(Identifier).name;
				l.popFront;
				l.front.expect(oper!"=");
				l.popFront;
				auto ty = parseType;
				ret.aliases[name] = ty;
			} else if (l.front == key!"auto" || l.front == key!"enum") {
				auto var = new ScopeVar();
				auto pos = l.front.pos;
				var.manifest = l.front == key!"enum";
				l.popFront;
				l.front.expectT!Identifier;
				var.name = l.front.get!(Identifier).name;
				l.popFront;
				l.front.expect(oper!"=");
				l.popFront;
				var.def = parseValue;
				var.pos = pos.join(l.front.pos);
				ret.states ~= Statement(var);
			} else if (l.front == key!"of") { //currently untested
				auto var = new ScopeVar();
				auto pos = l.front.pos;
				var.manifest = false;
				l.popFront;
				auto ty = parseType;
				l.front.expectT!Identifier;
				var.name = l.front.get!(Identifier).name;
				l.popFront;
				auto val = new Cast();
				val.wanted = ty;
				var.def = val;
				if (l.front == oper!"=") {
					l.popFront;
					val.value = parseValue;
				} else {
					val.value = new StructLit();
				}
				var.pos = pos.join(l.front.pos);
				ret.states ~= Statement(var);
			} else {
				auto val = parseValue(false);
				if (val is null) {
					error("Expected alias,variable decleration, or value", l.front.pos);
					return null;
				} else {
					ret.states ~= Statement(val);
				}
			}
			l.front.expect(oper!";");
			l.popFront;
		}
	}

	Value parseValueFuncLit() {
		auto pos = l.front.pos;
		if (l.front == oper!"$") {
			auto ret = new FuncLit();
			l.popFront;
			ret.fvar = new FuncLitVar;
			auto pos2 = l.front.pos;
			ret.fvar.ty = parseType;
			l.front.expectT!Identifier;
			ret.fvar.name = l.front.get!(Identifier).name;
			l.popFront;
			ret.fvar.pos = pos2.join(l.front.pos);
			ret.text = parseValue;

			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Value parseValueReturn() {
		if (l.front == key!"return") {
			auto ret = new Return();
			auto pos = l.front.pos;
			l.popFront;
			if (l.front == oper!".") {
				l.popFront;
				l.front.expectT!IntLiteral;
				ret.upper = l.front.get!(IntLiteral).num.toUInt;
				l.popFront;
			} else {
				ret.upper = uint.max;
			}
			ret.value = parseValue;
			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Value parseStringLit() {
		if (l.front.peek!StringLiteral) {
			auto ret = new StringLit;
			auto pos = l.front.pos;
			ret.str = l.front.get!(StringLiteral).data;
			l.popFront;
			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Value parseArrayLit() {
		auto val = parseValueStruct!(oper!"[", oper!"]");
		if (val) {
			auto ret = new ArrayLit;
			ret.values = (cast(StructLit) val).values;
			ret.pos = val.pos;
			return ret;
		}
		return null;
	}

	Value parseExtern() {
		if (l.front == key!"extern") {
			auto ret = new ExternJS;
			auto pos = l.front.pos;
			l.popFront;
			l.front.expectT!StringLiteral;
			auto str = l.front.get!(StringLiteral).data;
			if (str != "js") {
				error("Only extern js is supported", l.front.pos);
			}
			l.popFront;
			l.front.expect(key!"of");
			l.popFront;
			ret.type = parseType;
			l.front.expect(oper!"=");
			l.popFront;
			l.front.expectT!StringLiteral;
			ret.external = l.front.get!(StringLiteral).data;
			l.popFront;
			ret.pos = pos.join(l.front.pos);
			return ret;
		}
		return null;
	}

	Module parseModule() {
		auto ret = new Module();
		auto base = cast(Scope) parseValueScopeimp!(Eof());
		ret.aliases = base.aliases;
		ret.imports = base.imports;
		ret.staticimports = base.staticimports;
		ret.pos = base.pos;
		foreach (s; base.states) {
			if (s.peek!Value) {
				error("Executable code not allow at global scope", s.get!(Value).pos);
				return null;
			}
			auto var = s.get!ScopeVar;
			auto mvar = new ModuleVar;
			mvar.def = var.def;
			mvar.pos = var.pos;
			mvar.name = var.name;
			mvar.manifest = var.manifest;
			ret.vars[mvar.name] = mvar;
		}
		return ret;
	}
}

@trusted unittest { //types
	import std.file; //import error;import std.conv;
	auto lexer = Lexer("test/syntax/types", cast(string) read("test/syntax/types"));
	auto parser = Parser(lexer);
	auto ty = parser.parseType;
	assert(cast(Int) ty);
	assert((cast(Int) ty).size == 1);

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	ty = parser.parseType;
	assert(cast(UInt) ty);
	assert((cast(UInt) ty).size == 0);

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	ty = parser.parseType;
	assert(cast(Pointer) ty);
	{
		auto ty2 = (cast(Pointer) ty).type;
		assert(cast(UnknownType) ty2);
		auto ty3 = cast(UnknownType) ty2;
		assert(ty3.name == "MyType");
		assert(ty3.namespace == ["custom", "module"]);
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	ty = parser.parseType;
	assert(cast(Struct) ty);
	{
		auto ty2 = cast(Struct) ty;
		assert(ty2.names["x"] == 0);
		assert(cast(Int) ty2.types[0]);
		assert((cast(Int) ty2.types[0]).size == 1);

		assert(ty2.names["y"] == 1);
		assert(cast(Int) ty2.types[1]);
		assert((cast(Int) ty2.types[1]).size == 1);
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	ty = parser.parseType;
	assert(cast(SubType) ty);
	{
		auto ty2 = cast(SubType) ty;
		assert(cast(Pointer) ty2.type);
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;
	assert(parser.l.empty);
}

@trusted unittest { //values
	import std.file; //import error;import std.conv;
	auto lexer = Lexer("test/syntax/values", cast(string) read("test/syntax/values"));
	auto parser = Parser(lexer);
	auto val = parser.parseValue;
	assert(cast(IntLit) val);
	assert((cast(IntLit)(val)).value == BigInt("42"));

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(BoolLit) val);
	assert((cast(BoolLit) val).yes);

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(BoolLit) val);
	assert(!(cast(BoolLit) val).yes);

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(StructLit) val);
	{
		auto val2 = cast(StructLit) val;
		assert(val2.values.length == 2);
		assert(cast(IntLit) val2.values[0]);
		assert((cast(IntLit) val2.values[0]).value == BigInt("64"));

		assert(cast(BoolLit) val2.values[1]);
		assert((cast(BoolLit) val2.values[1]).yes);
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(Variable) val);
	assert((cast(Variable) val).name == "var");
	assert((cast(Variable) val).namespace == ["my", "test"]);

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(If) val);
	{
		auto val2 = cast(If) val;
		assert(cast(IntLit) val2.cond);
		assert((cast(IntLit) val2.cond).value == BigInt("0"));

		assert(cast(IntLit) val2.yes);
		assert((cast(IntLit) val2.yes).value == BigInt("1"));

		assert(cast(IntLit) val2.no);
		assert((cast(IntLit) val2.no).value == BigInt("2"));
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(While) val);
	{
		auto val2 = cast(While) val;
		assert(cast(IntLit) val2.cond);
		assert((cast(IntLit) val2.cond).value == BigInt("0"));

		assert(cast(IntLit) val2.state);
		assert((cast(IntLit) val2.state).value == BigInt("1"));

	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(New) val);
	assert(cast(IntLit)((cast(New) val).value));
	assert((cast(IntLit)(cast(New) val).value).value == BigInt("1"));

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(NewArray) val);
	{
		auto val2 = cast(NewArray) val;
		assert(cast(IntLit) val2.value);
		assert((cast(IntLit) val2.value).value == BigInt("2"));
		assert(cast(IntLit) val2.length);
		assert((cast(IntLit) val2.length).value == BigInt("0"));
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue; //todo finish asserts
	assert(cast(Scope) val);
	{
		auto val2 = cast(Scope) val;
		assert(val2.states.length == 2);
		assert(val2.states[0].peek!Value);
		assert(cast(IntLit) val2.states[0].get!(Value));
		assert(val2.states[1].peek!ScopeVar);
		assert(val2.states[1].get!(ScopeVar));

	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(Binary!"+") val);
	{
		auto val2 = cast(Binary!"+") val;
		assert(cast(IntLit) val2.left);
		assert(cast(Binary!"*") val2.right);
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(FuncLit) val);

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(Return) val);

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(Slice) val);
	{
		auto sli = cast(Slice) val;
		assert(cast(IntLit)(sli.array));
		assert(cast(IntLit)(sli.left));
		assert(cast(IntLit)(sli.right));
	}
	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(CharLit) val);
	{
		auto chlit = cast(CharLit) val;
		assert((cast(CharLit) val).value == 'b');
	}
	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(StringLit) val);
	{
		assert((cast(StringLit) val).str == "hello world");
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;

	val = parser.parseValue;
	assert(cast(ArrayLit) val);
	{
		auto arlit = cast(ArrayLit) val;
		assert(cast(IntLit) arlit.values[0]);
	}

	assert(parser.l.front == oper!";");
	parser.l.popFront;
	assert(parser.l.empty);
}

@trusted unittest {
	import std.file;
	import std.stdio;
	import error;
	import std.conv;

	auto lexer = Lexer("test/syntax/module", cast(string) read("test/syntax/module"));
	auto parser = Parser(lexer);

	@trusted Module importer(string[] str) {
		assert(str == ["my", "test", "module"]);
		return new Module();
	}

	parser.onImport = &importer;

	auto mod = parser.parseModule;
	@trusted void visiter(Node n, Trace sc) {
		//writeln(n.to!string,prettyPrint(n.pos));
		foreach (ch, subt; n.children(sc)) {
			visiter(ch, subt);
		}
	}

	visiter(mod, null);
	assert(["test"] in mod.staticimports);
}
