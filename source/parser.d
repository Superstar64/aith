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
import app : findAndReadModule;
import lexer;
import std.algorithm : countUntil;

struct Parser {
	Lexer lexer;

	Expression parseExpression() {
		with (lexer) {
			return parseBinary!("&&", "||", parseBinary!("==", "!=", "<=",
					">=", "<", ">", parseBinary!("+", "-", "~",
					parseBinary!("*", "/", "%", parsePrefix!("+", "-", "*", "/", "&", "!")))));
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

	Expression parsePrefix(opers...)() {
		with (lexer) {
			auto pos = front.pos;
			foreach (o; opers) {
				if (front == oper!o) {
					static if (o == "+" || o == "-") { //hacky special case
						auto original = lexer;
						bool usign = front == oper!"+";
						bool nega = front == oper!"-";
						popFront;
						auto intL = parseIntLit(usign, nega);
						if (intL) {
							intL.pos = pos.join(front.pos);
							return parsePostfix(intL);
						}
						lexer = original;
					}
					auto ret = new Prefix!o;
					popFront;
					ret.value = parsePrefix!(opers);
					ret.pos = pos.join(front.pos);
					return ret;
				}
			}
			return parseCore;
		}
	}

	Expression parseCore() {
		with (lexer) {
			Expression val;
			foreach (fun; AliasSeq!(parseBasic, parseCast, parseTuple!(oper!"(",
					oper!")"), parseVariable, parseIf, parseWhile,
					parseNew, parseScope, parseImport, parseFuncArgument, parseFuncLit,
					parseStringLit, parseArrayLit, parseExtern, parseBasicType, parseStruct)) {
				auto value = fun;
				if (value) {
					return parsePostfix(value);
				}
			}

			error("Expected expression", front.pos);
			assert(0);
		}
	}

	Expression parseStruct() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"struct") {
				auto ret = new Struct();
				popFront;
				ret.value = parseExpression();
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseBasicType() {
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
				auto int_t = new Int();
				int_t.size = parseDotFix;
				ret = int_t;
			} else if (front == key!"uint_t") {
				popFront;
				auto int_t = new UInt();
				int_t.size = parseDotFix;
				ret = int_t;
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

	Expression parseBasic() {
		with (lexer) {
			auto pos = front.pos;
			auto intL = parseIntLit;
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

	Expression parseIntLit(bool posi = false, bool nega = false) {
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

	Expression parseCast() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"cast") {
				auto ret = new Cast();
				popFront;
				front.expect(oper!"(");
				popFront;
				ret.wanted = parseExpression;
				front.expect(oper!")");
				popFront;
				ret.value = parseExpression;
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseTupleImpl() {
		with (lexer) {
			auto ret = new TupleLit();
			while (true) {
				ret.values ~= parseExpression;
				if (front != oper!",") {
					break;
				}
				popFront;
			}
			if (ret.values.length == 1) {
				return ret.values[0];
			}
			return ret;
		}
	}

	Expression parseTuple(alias Front = oper!"(", alias End = oper!")")() {
		with (lexer) {
			Expression val;
			auto pos = front.pos;
			if (front == Front) {
				popFront;
				if (front == End) {
					popFront;
					auto ret = new TupleLit();
					ret.pos = pos.join(front.pos);
					return ret;
				}
				val = parseTupleImpl;
				front.expect(End);
				popFront;
				val.pos = pos.join(front.pos);
			}
			return val;
		}
	}

	Expression parseFuncArgument() {
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

	Expression parseVariable() {
		with (lexer) {
			auto pos = front.pos;
			if (front.peek!Identifier) {
				auto ret = new Variable();
				ret.name = front.get!(Identifier).name;
				popFront;
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseIf() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"if") {
				auto ret = new If();
				popFront;
				ret.cond = parseExpression;
				front.expect(key!"then");
				popFront;
				ret.yes = parseExpression;
				if (front == key!"else") {
					popFront;
					ret.no = parseExpression;
				} else {
					ret.no = new TupleLit();
				}
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseWhile() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"while") {
				auto ret = new While();
				popFront;
				ret.cond = parseExpression;
				if (front == key!"then") {
					popFront;
					ret.state = parseExpression;
				} else {
					ret.state = new TupleLit();
				}
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseNew() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"new") {
				popFront;
				if (front == oper!"[") {
					auto ret = new NewArray();
					ret.length = parseTuple!(oper!"[", oper!"]");
					assert(ret.length);
					ret.value = parseExpression;
					ret.pos = pos.join(front.pos);
					return ret;
				} else {
					auto ret = new New();
					ret.value = parseExpression;
					ret.pos = pos.join(front.pos);
					return ret;
				}
			}
			return null;
		}
	}

	Expression parsePostfix(Expression current) {
		with (lexer) {
			auto pos = current.pos;
			if (front == oper!".") {
				auto ret = new Dot();
				ret.value = current;
				popFront;
				front.expectT!(Identifier);
				ret.index = front.get!(Identifier).name;
				popFront;
				ret.pos = pos.join(front.pos);
				return parsePostfix(ret);
			} else if (front == oper!"[") {
				auto pos2 = front.pos;
				popFront;
				if (front == oper!"]") {
					popFront;
					auto ret = new ArrayIndex;
					ret.array = current;
					ret.index = new TupleLit();
					ret.index.pos = pos2.join(front.pos);
					ret.pos = pos.join(front.pos);
					return parsePostfix(ret);
				}
				auto val = parseTupleImpl;
				if (front == oper!"..") {
					auto ret = new Slice;
					ret.array = current;
					ret.left = val;
					ret.left.pos = pos2.join(front.pos);

					popFront;
					pos2 = front.pos;

					ret.right = parseTupleImpl;
					front.expect(oper!"]");
					popFront;
					ret.right.pos = pos2.join(front.pos);
					ret.pos = pos.join(front.pos);
					return parsePostfix(ret);
				} else {
					assert(front == oper!"]");
					popFront;
					auto ret = new ArrayIndex;
					ret.array = current;
					ret.index = val;
					ret.index.pos = pos2.join(front.pos);
					ret.pos = pos.join(front.pos);
					return parsePostfix(ret);
				}
			} else if (front == oper!"(") {
				auto argument = parseTupleImpl;
				assert(argument);
				auto ret = new FuncCall();
				ret.fptr = current;
				ret.arg = argument;
				ret.pos = pos.join(front.pos);
				return parsePostfix(ret);
			} else if (front == oper!"(*)") {
				auto ret = new Postfix!"(*)"();
				popFront;
				ret.value = current;
				ret.pos = pos.join(front.pos);
				return parsePostfix(ret);
			}
			return current;
		}
	}

	Expression parseScope() {
		with (lexer) {
			auto pos = front.pos;
			if (front == oper!"{") {
				popFront;
				auto ret = parseScopeImpl!(oper!"}")();
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseScopeImpl(alias end = oper!"}")() {
		with (lexer) {
			auto ret = new Scope();
			while (true) {
				if (front == end) {
					popFront;
					return ret;
				}
				if (front == key!"let" || front == key!"alias") {
					auto var = new ScopeVarDef();
					parseVarDef(var, front == key!"alias");
					ret.states ~= var;
				} else {
					auto pos = front.pos;
					auto val = parseExpression;
					if (front == end) {
						ret.last = val;
						popFront;
						return ret;
					} else if (front == oper!"=") {
						popFront;
						auto assigner = parseExpression;
						auto assign = new Assign;
						assign.left = val;
						assign.right = assigner;
						assign.pos = pos.join(front.pos);
						ret.states ~= assign;
					} else {
						ret.states ~= val;
					}
				}
				front.expect(oper!";");
				popFront;
			}
		}
	}

	void parseVarDef(VarDef var, bool manifest) {
		with (lexer) {
			auto pos = front.pos;
			var.manifest = manifest;
			popFront;
			auto type = parseExpression();
			if (front != oper!"=") {
				front.expectT!Identifier;
				var.name = front.get!(Identifier).name;
				popFront;
				front.expect(oper!"=");
				popFront;
				var.explicitType = type;
			} else {
				assert(front == oper!"=");
				auto expr = cast(Variable) type;
				if (!expr) {
					error("expected identifier", pos);
				}
				var.name = expr.name;
				popFront;
			}

			var.definition = parseExpression();
			var.pos = pos.join(front.pos);
		}
	}

	Expression parseImport() {
		with (lexer) {
			auto pos = front.pos;
			if (front == key!"import") {
				auto ret = new Import();
				popFront;
				front.expectT!StringLiteral;
				auto file = front.get!StringLiteral.data;
				popFront();
				ret.mod = findAndReadModule(file);
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseFuncLit() {
		with (lexer) {
			auto pos = front.pos;
			if (front == oper!"$") {
				auto ret = new FuncLit();
				popFront;
				auto type = parseExpression;
				if (front == oper!"->") {
					popFront;
					ret.explict_return = type;
					type = parseExpression;
				}
				ret.argument = type;
				ret.text = parseExpression;

				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	Expression parseStringLit() {
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

	Expression parseArrayLit() {
		with (lexer) {
			auto val = parseTuple!(oper!"[", oper!"]");
			if (val) {
				auto ret = new ArrayLit;
				ret.values = (cast(TupleLit) val).values;
				ret.pos = val.pos;
				return ret;
			}
			return null;
		}
	}

	Expression parseExtern() {
		with (lexer) {
			if (front == key!"extern") {
				auto ret = new ExternJs;
				auto pos = front.pos;
				popFront;
				ret.pos = pos.join(front.pos);
				return ret;
			}
			return null;
		}
	}

	enum modifiersList = ["public", "private"];
	enum indexModifier(string modifier) = modifiersList.countUntil(modifier);
	static void applyModifiers(int[] modifiers, ref Modifier output) {
		foreach (modifier; modifiers) {
			if (modifier == indexModifier!"public") {
				output.visible = true;
			} else if (modifier == indexModifier!"private") {
				output.visible = false;
			} else {
				assert(0);
			}
		}
	}

	//todo this is ugly remove it
	void parseModule(Module ret) {
		with (lexer) {
			Modifier globalModifiers;
			while (true) {
				if (front == Eof()) {
					popFront;
					return;
				}
				int[] modifiersList;
				while (true) {
					if (front == key!"public") {
						modifiersList ~= indexModifier!"public";
					} else if (front == key!"private") {
						modifiersList ~= indexModifier!"private";
					} else {
						break;
					}
					popFront;
				}
				if (modifiersList.length > 0 && front == oper!":") {
					applyModifiers(modifiersList, globalModifiers);
					popFront;
				} else if (front == key!"let" || front == key!"alias") {
					Modifier localModifiers = globalModifiers;
					applyModifiers(modifiersList, localModifiers);
					auto var = new ModuleVarDef();
					var.modifier = localModifiers;
					parseVarDef(var, front == key!"alias");
					ret.symbols[var.name] = var;
					if (auto ext = cast(ExternJs) var.definition) {
						if (var.manifest) {
							ext.name = var.name;
						}
					}
					if (auto func = cast(FuncLit) var.definition) {
						func.name = var.name;
					}
					front.expect(oper!";");
					popFront;
				} else {
					error("Expected variable or modifiers list", front.pos);
				}
			}
		}
	}
}
