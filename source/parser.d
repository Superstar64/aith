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
module parser;

import std.bigint : BigInt;
import std.meta : AliasSeq;
import std.utf : decodeFront;
import error : error, Position;

import ast;
import lexer;

struct Parser {
	Lexer lexer;
	Module delegate(string[]) onImport;
	//todo rework parsing rules

	Expression parseType() {
		with (lexer) {
			foreach (fun; AliasSeq!(parseTypeBasic, parseTypeFunc,
					parseTypeStruct, parseTypeUnknown)) {
				auto type = fun();
				if (type) {
					return parseTypePostfix(type);
				}
			}
			error("Expected Type", front.pos);
			assert(0);
		}
	}

	Expression parseTypeBasic() {
		with (lexer) {
			uint parseDotFix() {
				if (front == oper!".") {
					popFront;
					uint res = front.expectT!(IntLiteral).toInt();
					popFront;
					return res;
				}
				return 0;
			}

			Expression ret;
			auto pos = front.pos;
			scope (exit) {
				if (ret) {
					ret.pos = pos.join(front.pos);
				}
			}
			if (front == key!"int_t") {
				popFront;
				ret = new Int(parseDotFix);
			} else if (front == key!"uint_t") {
				popFront;
				ret = new UInt(parseDotFix);
			} else if (front == key!"char") {
				popFront;
				ret = new Char();
			} else if (front == key!"bool_t") {
				popFront;
				ret = new Bool();
			}
			return ret;
		}
	}

	Expression parseTypePostfix(Expression current) {
		with (lexer) {
			auto pos = current.pos;
			if (front == oper!"*") {
				auto ret = new Pointer();
				popFront;
				ret.type = current;
				ret.pos = pos.join(front.pos);
				return parseTypePostfix(ret);
			} else if (front == oper!"[") {
				auto ret = new ArrayIndex();
				popFront;
				front.expect(oper!"]");
				popFront;
				ret.array = current;
				ret.index = new StructLit();
				ret.pos = pos.join(front.pos);
				return parseTypePostfix(ret);
			}
			return current;
		}
	}

	Expression parseTypeFunc() {
		with (lexer) {
			if (front == oper!"$") {
				auto ret = new FCall();
				auto pos = front.pos;
				scope (exit) {
					ret.pos = pos.join(front.pos);
				}
				popFront;
				ret.fptr = parseType();
				front.expect(oper!":");
				popFront;
				ret.arg = parseType();
				return ret;
			}
			return null;
		}
	}

	Expression parseTypeStruct() {
		with (lexer) {
			if (front == oper!"{") {
				auto ret = new StructLit();
				auto pos = front.pos;
				scope (exit) {
					ret.pos = pos.join(front.pos);
				}
				popFront;
				if (front != oper!"}") {
					uint count;
					while (true) {
						ret.values ~= parseType();
						if (front.peek!Identifier) {
							ret.names[front.get!(Identifier).name] = count;
							popFront;
						}
						if (front != oper!",") {
							break;
						}
						popFront;
						count++;
					}
					front.expect(oper!"}");
				}
				popFront;
				if (ret.values.length == 1 && ret.names.length == 0) {
					return ret.values[0];
				}
				return ret;
			}
			return null;
		}
	}

	Expression parseTypeUnknown() {
		with (lexer) {
			if (front.peek!Identifier) {
				auto ret = new Variable();
				auto pos = front.pos;
				scope (exit) {
					ret.pos = pos.join(front.pos);
				}
				while (true) {
					front.expectT!Identifier;
					ret.name = front.get!(Identifier).name;
					popFront;
					if (front != oper!"::") {
						break;
					}
					ret.namespace ~= ret.name;
					popFront;
				}
				return ret;
			}
			return null;
		}
	}

	Expression parseValue(bool nullable = false) {
		with (lexer) {
			return parseBinary!("=", parseBinary!("&&", "||", parseBinary!("==",
					"!=", "<=", ">=", "<", ">", parseBinary!("+", "-", "~",
					parseBinary!("*", "/", "%", parseValuePrefix!("+", "-", "*", "/", "&", "!"))))));
		}
	}

	Expression parseBinary(args...)() {
		with (lexer) {
			alias opers = args[0 .. $ - 1];
			alias sub = args[$ - 1];
			auto pos = front.pos;
			auto val = sub;
			foreach (o; opers) {
				if (front == oper!o) {
					auto ret = new Binary!o;
					popFront;
					ret.left = val;
					ret.right = parseBinary!args;
					ret.pos = pos.join(front.pos);
					return ret;
				}
			}
			return val;
		}
	}

	Expression parseValuePrefix(opers...)() {
		with (lexer) {
			auto pos = front.pos;
			foreach (o; opers) {
				if (front == oper!o) {
					static if (o == "+" || o == "-") { //hacky special case
						auto original = lexer;
						bool usign = front == oper!"+";
						bool nega = front == oper!"-";
						popFront;
						auto intL = parseValueIntLit(usign, nega);
						if (intL) {
							intL.pos = pos.join(front.pos);
							return parseValuePostfix(intL);
						}
						lexer = original;
					}
					auto ret = new Prefix!o;
					popFront;
					ret.value = parseValuePrefix!(opers);
					ret.pos = pos.join(front.pos);
					return ret;
				}
			}
			return parseValueCore;
		}
	}

	Expression parseValueCore(bool nullable = false) {
		with (lexer) {
			Expression val;
			foreach (fun; AliasSeq!(parseValueBasic, parseValueCast,
					parseValueStruct!(oper!"(", oper!")"), parseValueVar, parseValueIf,
					parseValueWhile, parseValueNew, parseValueScope,
					parseValueFuncArgument, parseValueFuncLit,
					parseValueStringLit, parseValueArrayLit, parseValueExtern)) {
				auto value = fun;
				if (value) {
					return parseValuePostfix(value);
				}
			}

			if (nullable) {
				return null;
			} else {
				error("Expected Value", front.pos);
				assert(0);
			}
		}
	}

	Expression parseValueBasic() {
		with (lexer) {
			auto pos = front.pos;
			auto intL = parseValueIntLit;
			if (intL) {
				intL.pos = pos.join(front.pos);
				return intL;
			} else if (front == key!"true") {
				auto ret = new BoolLit();
				ret.yes = true;
				popFront;
				ret.pos = pos.join(front.pos);
				return ret;
			} else if (front == key!"false") {
				auto ret = new BoolLit();
				ret.yes = false;
				popFront;
				ret.pos = pos.join(front.pos);
				return ret;
			} else if (front.peek!CharLiteral) {
				auto ret = new CharLit();
				auto str = front.get!(CharLiteral).data;
				ret.value = decodeFront(str);
				if (str.length != 0) {
					error("Char Lit to big", front.pos);
				}
				popFront;
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueIntLit(bool posi = false, bool nega = false) {
		with (lexer) {
			if (front.peek!IntLiteral) {
				auto ret = new IntLit;
				ret.value = front.get!(IntLiteral).num;
				ret.usigned = posi;
				if (nega) {
					ret.value = -ret.value;
				}
				popFront;
				return ret;
			}
			return null;
		}
	}

	Expression parseValueCast() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"cast") {
				auto ret = new Cast();
				popFront;
				front.expect(oper!"(");
				popFront;
				ret.wanted = parseType;
				front.expect(oper!")");
				popFront;
				ret.value = parseValue;
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueStructimp() {
		with (lexer) {
			auto ret = new StructLit();
			while (true) {
				ret.values ~= parseValue();
				if (front != oper!",") {
					break;
				}
				popFront;
			}
			if (ret.values.length == 1 && ret.names.length == 0) {
				return ret.values[0];
			}
			return ret;
		}
	}

	Expression parseValueStruct(alias Front = oper!"(", alias End = oper!")")() {
		with (lexer) {
			Expression val;
			auto pos = front.pos;
			if (front == Front) {
				popFront;
				if (front == End) {
					popFront;
					return new StructLit();
				}
				val = parseValueStructimp;
				front.expect(End);
				popFront;
				val.pos = pos.join(front.pos);
			}
			return val;
		}
	}

	Expression parseValueFuncArgument() {
		with (lexer) {
			if (front == oper!"$@") {
				auto ret = new FuncArgument();
				auto pos = front.pos;
				popFront;
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueVar() {
		with (lexer) {
			auto pos = front.pos;
			if (front.peek!Identifier) {
				auto ret = new Variable();
				while (true) {
					ret.name = front.get!(Identifier).name;
					popFront;
					if (front != oper!"::") {
						break;
					}
					popFront;
					ret.namespace ~= ret.name;
				}
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueIf() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"if") {
				auto ret = new If();
				popFront;
				ret.cond = parseValue;
				front.expect(key!"then");
				popFront;
				ret.yes = parseValue;
				if (front == key!"else") {
					popFront;
					ret.no = parseValue;
				} else {
					ret.no = new StructLit();
				}
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueWhile() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"while") {
				auto ret = new While();
				popFront;
				ret.cond = parseValue;
				if (front == key!"then") {
					popFront;
					ret.state = parseValue;
				} else {
					ret.state = new StructLit();
				}
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueNew() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"new") {
				popFront;
				if (front == oper!"[") {
					auto ret = new NewArray();
					ret.length = parseValueStruct!(oper!"[", oper!"]");
					assert(ret.length);
					ret.value = parseValue;
					ret.pos = pos.join(front.pos);
					return ret;
				} else {
					auto ret = new New();
					ret.value = parseValue;
					ret.pos = pos.join(front.pos);
					return ret;
				}
			}
			return null;
		}
	}

	Expression parseValuePostfix(Expression current) {
		with (lexer) {
			auto pos = current.pos;
			if (front == oper!".") {
				auto ret = new Dot();
				ret.value = current;
				popFront;
				front.expectT!(IntLiteral, Identifier);
				if (front.peek!Identifier) {
					ret.index = front.get!(Identifier).name;
				} else {
					ret.index = front.get!(IntLiteral).num;
				}
				popFront;
				ret.pos = pos.join(front.pos);
				return parseValuePostfix(ret);
			} else if (front == oper!"[") {
				auto pos2 = front.pos;
				popFront;
				if (front == oper!"]") {
					popFront;
					auto ret = new ArrayIndex;
					ret.array = current;
					ret.index = new StructLit();
					ret.index.pos = pos2.join(front.pos);
					ret.pos = pos.join(front.pos);
					return parseValuePostfix(ret);
				}
				auto val = parseValueStructimp;
				if (front == oper!"..") {
					auto ret = new Slice;
					ret.array = current;
					ret.left = val;
					ret.left.pos = pos2.join(front.pos);

					popFront;
					pos2 = front.pos;

					ret.right = parseValueStructimp;
					front.expect(oper!"]");
					popFront;
					ret.right.pos = pos2.join(front.pos);
					ret.pos = pos.join(front.pos);
					return parseValuePostfix(ret);
				} else {
					assert(front == oper!"]");
					popFront;
					auto ret = new ArrayIndex;
					ret.array = current;
					ret.index = val;
					ret.index.pos = pos2.join(front.pos);
					ret.pos = pos.join(front.pos);
					return parseValuePostfix(ret);
				}
			} else if (front == oper!"(") {
				auto tmp = parseValueCore(true);
				if (tmp) {
					auto ret = new FCall();
					ret.fptr = current;
					ret.arg = tmp;
					ret.pos = pos.join(front.pos);
					return parseValuePostfix(ret);
				}
			}
			return current;
		}
	}

	Expression parseValueScope() {
		with (lexer) {
			auto pos = front.pos;
			if (front == oper!"{") {
				popFront;
				auto ret = parseValueScopeimp!(oper!"}")();
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueScopeimp(alias end = oper!"}")() {
		with (lexer) {
			auto ret = new Scope();
			while (true) {
				if (front == end) {
					popFront;
					return ret;
				}
				if (front == key!"import") {
					popFront;
					string[] namespace;
					while (front.expectT!(Identifier)) {
						namespace ~= front.get!(Identifier).name;
						popFront;
						if (front == oper!"::") {
							popFront;
							continue;
						}
						break;
					}
					if (front == oper!"=") {
						popFront;
						string[] name;
						name = namespace;
						namespace = null;
						while (front.expectT!(Identifier)) {
							namespace ~= front.get!(Identifier).name;
							popFront;
							if (front == oper!"::") {
								popFront;
								continue;
							}
							break;
						}
						ret.staticimports[name.idup] ~= onImport(namespace);
					} else {
						ret.imports ~= onImport(namespace);
					}

				} else if (front == key!"alias") {
					auto var = new ScopeVar();
					auto pos = front.pos;
					popFront;
					front.expectT!Identifier;
					auto name = front.get!(Identifier).name;
					var.manifest = true;
					var.name = name;
					popFront;
					front.expect(oper!"=");
					popFront;
					var.definition = parseType;
					ret.symbols[name] = var;
				} else if (front == key!"auto" || front == key!"enum") {
					auto var = new ScopeVar();
					auto pos = front.pos;
					var.manifest = front == key!"enum";
					popFront;
					front.expectT!Identifier;
					var.name = front.get!(Identifier).name;
					popFront;
					front.expect(oper!"=");
					popFront;
					var.definition = parseValue;
					var.pos = pos.join(front.pos);
					ret.states ~= var;
				} else if (front == key!"of") {
					auto var = new ScopeVar();
					auto pos = front.pos;
					var.manifest = false;
					popFront;
					auto ty = parseType;
					front.expectT!Identifier;
					var.name = front.get!(Identifier).name;
					popFront;
					auto val = new Cast();
					val.wanted = ty;
					var.definition = val;
					if (front == oper!"=") {
						popFront;
						val.value = parseValue;
					} else {
						val.value = new StructLit();
					}
					var.pos = pos.join(front.pos);
					ret.states ~= var;
				} else {
					auto val = parseValue(false);
					if (val is null) {
						error("Expected alias,variable decleration, or value", front.pos);
						return null;
					} else {
						if (front == end) {
							ret.last = val;
							popFront;
							return ret;
						} else {
							ret.states ~= val;
						}
					}
				}
				front.expect(oper!";");
				popFront;
			}
		}
	}

	Expression parseValueFuncLit() {
		with (lexer) {
			auto pos = front.pos;
			if (front == oper!"$") {
				auto ret = new FuncLit();
				popFront;
				auto type = parseType;
				if (front == oper!"->") {
					popFront;
					ret.explict_return = type;
					type = parseType;
				}
				ret.argument = type;
				ret.text = parseValue;

				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueStringLit() {
		with (lexer) {
			if (front.peek!StringLiteral) {
				auto ret = new StringLit;
				auto pos = front.pos;
				ret.str = front.get!(StringLiteral).data;
				popFront;
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseValueArrayLit() {
		with (lexer) {
			auto val = parseValueStruct!(oper!"[", oper!"]");
			if (val) {
				auto ret = new ArrayLit;
				ret.values = (cast(StructLit) val).values;
				ret.pos = val.pos;
				return ret;
			}
			return null;
		}
	}

	Expression parseValueExtern() {
		with (lexer) {
			if (front == key!"extern") {
				auto ret = new ExternJS;
				auto pos = front.pos;
				popFront;
				front.expectT!StringLiteral;
				auto str = front.get!(StringLiteral).data;
				if (str != "js") {
					error("Only extern js is supported", front.pos);
				}
				popFront;
				front.expect(key!"of");
				popFront;
				ret.type = parseType;
				front.expect(oper!"=");
				popFront;
				front.expectT!StringLiteral;
				ret.external = front.get!(StringLiteral).data;
				popFront;
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	//todo this is ugly remove it
	Module parseModule(string[] namespace) {
		with (lexer) {
			auto ret = new Module();
			auto base = cast(Scope) parseValueScopeimp!(Eof());
			foreach (name, symbol; base.symbols) {
				ret.symbols[name] = new ModuleVar();
				ret.symbols[name].name = symbol.name;
				ret.symbols[name].heap = symbol.heap;
				ret.symbols[name].manifest = symbol.manifest;
				ret.symbols[name].definition = symbol.definition;
			}
			ret.imports = base.imports;
			ret.staticimports = base.staticimports;
			ret.namespace = namespace;
			foreach (state; base.states) {
				if (auto value = cast(Expression) state) {
					error("Executable code not allow at global scope", value.pos);
					return null;
				}
				auto var = cast(ScopeVar) state;
				auto mvar = new ModuleVar;
				mvar.definition = var.definition;
				mvar.pos = var.pos;
				mvar.name = var.name;
				mvar.manifest = var.manifest;
				mvar.namespace = namespace;
				ret.symbols[mvar.name] = mvar;
			}
			return ret;
		}
	}
}
