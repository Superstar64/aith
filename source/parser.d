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
			auto position = front.position;
			auto val = sub;
			foreach (o; opers) {
				if (front == oper!o) {
					auto ret = new Binary!o;
					popFront;
					ret.left = val;
					ret.right = parseBinary!args;
					ret.position = position.join(front.position);
					return ret;
				}
			}
			return val;
		}
	}

	Expression parsePrefix(opers...)() {
		with (lexer) {
			auto position = front.position;
			foreach (o; opers) {
				if (front == oper!o) {
					static if (o == "+" || o == "-") { //hacky special case
						auto original = lexer;
						bool usign = front == oper!"+";
						bool nega = front == oper!"-";
						popFront;
						auto intL = parseIntLit(usign, nega);
						if (intL) {
							intL.position = position.join(front.position);
							return parsePostfix(intL);
						}
						lexer = original;
					}
					auto ret = new Prefix!o;
					popFront;
					ret.value = parsePrefix!(opers);
					ret.position = position.join(front.position);
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

			error("Expected expression", front.position);
			assert(0);
		}
	}

	Expression parseStruct() {
		with (lexer) {
			auto position = front.position;
			if (front == key!"struct") {
				auto ret = new TypeTemporaryStruct();
				popFront;
				ret.value = parseExpression();
				ret.position = position.join(front.position);
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
			auto position = front.position;
			scope (exit) {
				if (ret) {
					ret.position = position.join(front.position);
				}
			}
			if (front == key!"int_t") {
				popFront;
				auto int_t = new TypeInt();
				int_t.size = parseDotFix;
				ret = int_t;
			} else if (front == key!"uint_t") {
				popFront;
				auto int_t = new TypeUInt();
				int_t.size = parseDotFix;
				ret = int_t;
			} else if (front == key!"char") {
				popFront;
				ret = new TypeChar();
			} else if (front == key!"bool_t") {
				popFront;
				ret = new TypeBool();
			}
			return ret;
		}
	}

	Expression parseBasic() {
		with (lexer) {
			auto position = front.position;
			auto intL = parseIntLit;
			if (intL) {
				intL.position = position.join(front.position);
				return intL;
			} else if (front == key!"true") {
				auto ret = new BoolLit();
				ret.yes = true;
				popFront;
				ret.position = position.join(front.position);
				return ret;
			} else if (front == key!"false") {
				auto ret = new BoolLit();
				ret.yes = false;
				popFront;
				ret.position = position.join(front.position);
				return ret;
			} else if (front.peek!CharLiteral) {
				auto ret = new CharLit();
				auto str = front.get!(CharLiteral).data;
				ret.value = decodeFront(str);
				if (str.length != 0) {
					error("TypeChar Lit to big", front.position);
				}
				popFront;
				ret.position = position.join(front.position);
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
			auto position = front.position;
			if (front == key!"cast") {
				auto ret = new Cast();
				popFront;
				front.expect(oper!"(");
				popFront;
				ret.wanted = parseExpression;
				front.expect(oper!")");
				popFront;
				ret.value = parseExpression;
				ret.position = position.join(front.position);
				return ret;
			}
			return null;
		}
	}

	Expression parseTupleImpl() {
		with (lexer) {
			auto ret = new TupleLit();
			while (true) {
				ret.values ~= Replaceable!Expression(parseExpression);
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
			auto position = front.position;
			if (front == Front) {
				popFront;
				if (front == End) {
					popFront;
					auto ret = new TupleLit();
					ret.position = position.join(front.position);
					return ret;
				}
				val = parseTupleImpl;
				front.expect(End);
				popFront;
				val.position = position.join(front.position);
			}
			return val;
		}
	}

	Expression parseFuncArgument() {
		with (lexer) {
			if (front == oper!"$@") {
				auto ret = new FuncArgument();
				auto position = front.position;
				popFront;
				ret.position = position.join(front.position);
				return ret;
			}
			return null;
		}
	}

	Expression parseVariable() {
		with (lexer) {
			auto position = front.position;
			if (front.peek!Identifier) {
				auto ret = new Variable();
				ret.name = front.get!(Identifier).name;
				popFront;
				ret.position = position.join(front.position);
				return ret;
			}
			return null;
		}
	}

	Expression parseIf() {
		with (lexer) {
			auto position = front.position;
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
				ret.position = position.join(front.position);
				return ret;
			}
			return null;
		}
	}

	Expression parseWhile() {
		with (lexer) {
			auto position = front.position;
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
				ret.position = position.join(front.position);
				return ret;
			}
			return null;
		}
	}

	Expression parseNew() {
		with (lexer) {
			auto position = front.position;
			if (front == key!"new") {
				popFront;
				if (front == oper!"[") {
					auto ret = new NewArray();
					ret.length = parseTuple!(oper!"[", oper!"]");
					assert(ret.length);
					ret.value = parseExpression;
					ret.position = position.join(front.position);
					return ret;
				} else {
					auto ret = new New();
					ret.value = parseExpression;
					ret.position = position.join(front.position);
					return ret;
				}
			}
			return null;
		}
	}

	Expression parsePostfix(Expression current) {
		with (lexer) {
			auto position = current.position;
			if (front == oper!".") {
				auto ret = new Dot();
				ret.value = current;
				popFront;
				front.expectT!(Identifier);
				ret.index = front.get!(Identifier).name;
				popFront;
				ret.position = position.join(front.position);
				return parsePostfix(ret);
			} else if (front == oper!"[") {
				auto pos2 = front.position;
				popFront;
				if (front == oper!"]") {
					popFront;
					auto ret = new Index;
					ret.array = current;
					ret.index = new TupleLit();
					ret.index.position = pos2.join(front.position);
					ret.position = position.join(front.position);
					return parsePostfix(ret);
				}
				auto val = parseTupleImpl;
				if (front == oper!"..") {
					auto ret = new Slice;
					ret.array = current;
					ret.left = val;
					ret.left.position = pos2.join(front.position);

					popFront;
					pos2 = front.position;

					ret.right = parseTupleImpl;
					front.expect(oper!"]");
					popFront;
					ret.right.position = pos2.join(front.position);
					ret.position = position.join(front.position);
					return parsePostfix(ret);
				} else {
					assert(front == oper!"]");
					popFront;
					auto ret = new Index;
					ret.array = current;
					ret.index = val;
					ret.index.position = pos2.join(front.position);
					ret.position = position.join(front.position);
					return parsePostfix(ret);
				}
			} else if (front == oper!"(") {
				auto argument = parseTupleImpl;
				assert(argument);
				auto ret = new Call();
				ret.fptr = current;
				ret.arg = argument;
				ret.position = position.join(front.position);
				return parsePostfix(ret);
			} else if (front == oper!"(*)") {
				auto ret = new Postfix!"(*)"();
				popFront;
				ret.value = current;
				ret.position = position.join(front.position);
				return parsePostfix(ret);
			}
			return current;
		}
	}

	Expression parseScope() {
		with (lexer) {
			auto position = front.position;
			if (front == oper!"{") {
				popFront;
				auto ret = parseScopeImpl!(oper!"}")();
				ret.position = position.join(front.position);
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
					ret.states ~= Replaceable!Statement(var);
				} else {
					auto position = front.position;
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
						assign.position = position.join(front.position);
						ret.states ~= Replaceable!Statement(assign);
					} else {
						ret.states ~= Replaceable!Statement(val);
					}
				}
				front.expect(oper!";");
				popFront;
			}
		}
	}

	void parseVarDef(VarDef var, bool manifest) {
		with (lexer) {
			auto position = front.position;
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
					error("expected identifier", position);
				}
				var.name = expr.name;
				popFront;
			}

			var.definition = parseExpression();
			var.position = position.join(front.position);
		}
	}

	Expression parseImport() {
		with (lexer) {
			auto position = front.position;
			if (front == key!"import") {
				auto ret = new Import();
				popFront;
				front.expectT!StringLiteral;
				auto file = front.get!StringLiteral.data;
				popFront();
				ret.mod = findAndReadModule(file);
				ret.position = position.join(front.position);
				return ret;
			}
			return null;
		}
	}

	Expression parseFuncLit() {
		with (lexer) {
			auto position = front.position;
			if (front == oper!"$") {
				auto ret = new FuncLit();
				popFront;
				auto type = parseExpression;
				if (front == oper!"->") {
					popFront;
					ret.explicit_return = type;
					type = parseExpression;
				}
				ret.argument = type;
				ret.text = parseExpression;

				ret.position = position.join(front.position);
				return ret;
			}
			return null;
		}
	}

	Expression parseStringLit() {
		with (lexer) {
			if (front.peek!StringLiteral) {
				auto ret = new StringLit;
				auto position = front.position;
				ret.str = front.get!(StringLiteral).data;
				popFront;
				ret.position = position.join(front.position);
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
				ret.position = val.position;
				return ret;
			}
			return null;
		}
	}

	Expression parseExtern() {
		with (lexer) {
			if (front == key!"extern") {
				auto ret = new ExternJs;
				auto position = front.position;
				popFront;
				ret.position = position.join(front.position);
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
					error("Expected variable or modifiers list", front.position);
				}
			}
		}
	}
}
