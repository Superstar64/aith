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

template dispatchLexer(alias fun, Types...) {
	auto dispatchLexer(T...)(ref Lexer lexer, auto ref T args) {
		foreach (Type; Types) {
			if (auto pointer = lexer.front.peek!Type) {
				lexer.popFront;
				return fun(*pointer, lexer, args);
			}
		}
		assert(0, T.stringof);
	}
}

template dispatchLexerFailable(alias fun, Types...) {
	auto dispatchLexerFailable(Fail, T...)(Fail fail, ref Lexer lexer, auto ref T args) {
		foreach (Type; Types) {
			if (auto pointer = lexer.front.peek!Type) {
				lexer.popFront;
				return fun(*pointer, lexer, args);
			}
		}
		return fail;
	}
}

template parseWrap(alias fun) {
	auto parseWrap(T...)(ref Lexer lexer, T args) {
		auto position = lexer.front.position;
		auto value = fun(lexer, args);
		if (value) {
			value.position = position.join(lexer.front.position);
		}
		return value;
	}
}

alias parseExpression = parseWrap!parseExpressionImpl;
Expression parseExpressionImpl(ref Lexer lexer) {
	return parseBinary!("&&", "||", parseBinary!("==", "!=", "<=", ">=", "<",
			">", parseBinary!("+", "-", "~", parseBinary!("*", "/", "%",
			parsePrefix!("+", "-", "*", "/", "&", "!")))))(lexer);
}

Expression parseBinary(args...)(ref Lexer lexer) {
	return parseWrap!(parseBinaryImpl!(args))(lexer);
}

Expression parseBinaryImpl(args...)(ref Lexer lexer) {
	alias opers = args[0 .. $ - 1];
	alias sub = args[$ - 1];
	auto val = sub(lexer);
	foreach (o; opers) {
		if (lexer.front == operator!o) {
			auto ret = new Binary!o;
			lexer.popFront;
			ret.left = val;
			ret.right = parseBinary!args(lexer);
			return ret;
		}
	}
	return val;
}

Expression parsePrefix(opers...)(ref Lexer lexer) {
	return parseWrap!(parsePrefixImpl!(opers))(lexer);
}

Expression parsePrefixImpl(opers...)(ref Lexer lexer) {
	foreach (o; opers) {
		if (lexer.front == operator!o) {
			static if (o == "+" || o == "-") { //hacky special case
				auto original = lexer;
				bool usign = lexer.front == operator!"+";
				bool nega = lexer.front == operator!"-";
				lexer.popFront;
				lexer.front.expectType!IntLiteral;
				auto intL = parseCoreDispatch(lexer.front.get!IntLiteral, lexer, usign, nega);
				if (intL) {
					return parsePostfix(lexer, intL);
				}
				lexer = original;
			}
			auto ret = new Prefix!o;
			lexer.popFront;
			ret.value = parsePrefix!(opers)(lexer);
			return ret;
		}
	}
	return parseWithPostfix(lexer);
}

alias parseWithPostfix = parseWrap!parseWithPostfixImpl;
Expression parseWithPostfixImpl(ref Lexer lexer) {
	return parsePostfix(lexer, parseCore(lexer));
}

alias parseCore = parseWrap!parseCoreImpl;
Expression parseCoreImpl(ref Lexer lexer) {
	auto value = dispatchLexerFailable!(parseCoreDispatch, Keyword!"struct", Keyword!"int_t", Keyword!"uint_t",
			Keyword!"char", Keyword!"bool_t", IntLiteral, Keyword!"true", Keyword!"false", CharLiteral,
			Keyword!"cast", Operator!"(", Operator!"$@", Identifier, Keyword!"if",
			Keyword!"while", Keyword!"new", Keyword!"import", Operator!"$",
			StringLiteral, Operator!"[", Keyword!"extern", Operator!"{")(null, lexer);
	if (value) {
		return value;
	}

	error("Expected expression", lexer.front.position);
	assert(0);
}

Expression parseCoreDispatch(Keyword!"struct", ref Lexer lexer) {
	auto ret = new TypeTemporaryStruct();
	ret.value = parseExpression(lexer);
	return ret;
}

uint parseDotFix(ref Lexer lexer) {
	if (lexer.front == operator!".") {
		lexer.popFront;
		uint res = lexer.front.expectType!(IntLiteral).toInt();
		lexer.popFront;
		return res;
	}
	assert(0);
}

Expression parseCoreDispatch(Keyword!"int_t", ref Lexer lexer) {
	auto int_t = new TypeInt();
	int_t.size = parseDotFix(lexer);
	return int_t;

}

Expression parseCoreDispatch(Keyword!"uint_t", ref Lexer lexer) {
	auto int_t = new TypeUInt();
	int_t.size = parseDotFix(lexer);
	return int_t;
}

Expression parseCoreDispatch(Keyword!"char", ref Lexer lexer) {
	return new TypeChar();
}

Expression parseCoreDispatch(Keyword!"bool_t", ref Lexer lexer) {
	return new TypeBool();
}

Expression parseCoreDispatch(IntLiteral value, ref Lexer lexer, bool posi = false, bool nega = false) {
	auto ret = new IntLit;
	ret.value = value;
	ret.usigned = posi;
	if (nega) {
		ret.value = -ret.value;
	}
	return ret;
}

Expression parseCoreDispatch(Keyword!"true", ref Lexer lexer) {
	auto ret = new BoolLit();
	ret.yes = true;
	return ret;
}

Expression parseCoreDispatch(Keyword!"false", ref Lexer lexer) {
	auto ret = new BoolLit();
	ret.yes = false;
	return ret;
}

Expression parseCoreDispatch(CharLiteral value, ref Lexer lexer) {
	auto ret = new CharLit();
	ret.value = decodeFront(value.value);
	if (value.value.length != 0) {
		error("TypeChar Lit to big", lexer.front.position);
	}
	return ret;
}

Expression parseCoreDispatch(Keyword!"cast", ref Lexer lexer) {
	auto ret = new Cast();
	lexer.front.expect(operator!"(");
	lexer.popFront;
	ret.wanted = parseExpression(lexer);
	lexer.front.expect(operator!")");
	lexer.popFront;
	ret.value = parseExpression(lexer);
	return ret;
}

Replaceable!Expression[] parseList(ref Lexer lexer) {
	Replaceable!Expression[] result;
	while (true) {
		result ~= Replaceable!Expression(parseExpression(lexer));
		if (lexer.front != operator!",") {
			break;
		}
		lexer.popFront;
	}
	return result;
}

Expression parseCoreDispatch(End...)(Operator!"(", ref Lexer lexer) {
	auto result = parseTupleEnd!(operator!")")(lexer);
	lexer.popFront;
	return result;
}

Expression parseTupleEnd(End...)(ref Lexer lexer) {
	foreach (stop; End) {
		if (lexer.front == stop) {
			auto ret = new TupleLit();
			return ret;
		}
	}
	auto list = parseList(lexer);
	lexer.front.expect(End);
	if (list.length == 1) {
		return list[0];
	} else {
		auto result = new TupleLit();
		result.values = list;
		return result;
	}
}

Expression parseTuple(alias Start, End...)(ref Lexer lexer) {
	return parseWrap!(parseTupleImpl!(Start, End))(lexer);
}

Expression parseTupleImpl(alias Start, End...)(ref Lexer lexer) {
	assert(lexer.front == Start);
	lexer.popFront;
	auto result = parseTupleEnd!End(lexer);
	lexer.popFront;
	return result;
}

Expression parseCoreDispatch(Operator!"$@", ref Lexer lexer) {
	return new FuncArgument();
}

Expression parseCoreDispatch(Identifier identifier, ref Lexer lexer) {
	auto ret = new Variable();
	ret.name = identifier.value;
	return ret;
}

Expression parseCoreDispatch(Keyword!"if", ref Lexer lexer) {
	auto ret = new If();
	ret.cond = parseExpression(lexer);
	lexer.front.expect(keyword!"then");
	lexer.popFront;
	ret.yes = parseExpression(lexer);
	if (lexer.front == keyword!"else") {
		lexer.popFront;
		ret.no = parseExpression(lexer);
	} else {
		ret.no = new TupleLit();
	}
	return ret;
}

Expression parseCoreDispatch(Keyword!"while", ref Lexer lexer) {
	auto ret = new While();
	ret.cond = parseExpression(lexer);
	if (lexer.front == keyword!"then") {
		lexer.popFront;
		ret.state = parseExpression(lexer);
	} else {
		ret.state = new TupleLit();
	}
	return ret;
}

Expression parseCoreDispatch(Keyword!"new", ref Lexer lexer) {
	if (lexer.front == operator!"[") {
		auto ret = new NewArray();
		ret.length = parseTuple!(operator!"[", operator!"]")(lexer);
		assert(ret.length);
		ret.value = parseExpression(lexer);
		return ret;
	} else {
		auto ret = new New();
		ret.value = parseExpression(lexer);
		return ret;
	}
}

Expression parseCoreDispatch(Keyword!"import", ref Lexer lexer) {
	auto ret = new Import();
	lexer.front.expectType!StringLiteral;
	auto file = lexer.front.get!StringLiteral.value;
	lexer.popFront();
	ret.mod = findAndReadModule(file);
	return ret;
}

Expression parseCoreDispatch(Operator!"$", ref Lexer lexer) {
	auto ret = new FuncLit();
	auto type = parseExpression(lexer);
	if (lexer.front == operator!"->") {
		lexer.popFront;
		ret.explicit_return = type;
		type = parseExpression(lexer);
	}
	ret.argument = type;
	ret.text = parseExpression(lexer);

	return ret;
}

Expression parseCoreDispatch(StringLiteral value, ref Lexer lexer) {
	auto ret = new StringLit;
	ret.str = value.value;
	return ret;
}

Expression parseCoreDispatch(Operator!"[", ref Lexer lexer) {
	auto val = parseTupleEnd!(operator!"]")(lexer);
	lexer.popFront;
	auto ret = new ArrayLit;
	ret.values = (cast(TupleLit) val).values;
	return ret;
}

Expression parseCoreDispatch(Keyword!"extern", ref Lexer lexer) {
	return new ExternJs;
}

Expression parsePostfix(ref Lexer lexer, Expression current) {
	return dispatchLexerFailable!(parsePostfixDispatch, Operator!".",
			Operator!"[", Operator!"(", Operator!"(*)")(current, lexer, current);
}

Expression parsePostfixDispatch(T)(T operator, ref Lexer lexer, Expression current) {
	auto result = parsePostfix(lexer, parsePostfixDispatchImpl(operator, lexer,
			current, lexer.front.position));
	result.position = current.position.join(lexer.front.position);
	return result;
}

Expression parsePostfixDispatchImpl(Operator!".", ref Lexer lexer,
		Expression current, Position postfixStart) {
	auto ret = new Dot();
	ret.value = current;
	lexer.front.expectType!(Identifier);
	ret.index = lexer.front.get!(Identifier).value;
	lexer.popFront;
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"[", ref Lexer lexer,
		Expression current, Position postfixStart) {
	auto argument = parseTupleEnd!(operator!"]", operator!"..")(lexer);
	return dispatchLexer!(parsePostfixBraceDispatch, Operator!"]", Operator!"..")(lexer,
			current, argument, postfixStart);
}

Expression parsePostfixBraceDispatch(Operator!"..", ref Lexer lexer,
		Expression current, Expression argument, Position postfixStart) {
	auto ret = new Slice;
	ret.array = current;
	ret.left = argument;
	ret.left.position = postfixStart.join(lexer.front.position);
	ret.right = parseTupleEnd!(operator!"]")(lexer);
	lexer.popFront;
	ret.right.position = postfixStart.join(lexer.front.position);
	return ret;
}

Expression parsePostfixBraceDispatch(Operator!"]", ref Lexer lexer,
		Expression current, Expression argument, Position postfixStart) {
	auto ret = new Index;
	ret.array = current;
	ret.index = argument;
	ret.index.position = postfixStart.join(lexer.front.position);
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"(", ref Lexer lexer,
		Expression current, Position postfixStart) {
	auto argument = parseTupleEnd!(operator!")")(lexer);
	assert(lexer.front == operator!")");
	lexer.popFront;
	auto ret = new Call();
	ret.fptr = current;
	ret.arg = argument;
	argument.position = postfixStart.join(lexer.front.position);
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"(*)", ref Lexer lexer, Expression current, Position) {
	auto ret = new Postfix!"(*)"();
	ret.value = current;
	return ret;
}

Expression parseCoreDispatch(Operator!"{", ref Lexer lexer) {
	auto ret = new Scope();
	while (true) {
		if (lexer.front == operator!"}") {
			lexer.popFront;
			return ret;
		}
		if (lexer.front == keyword!"let" || lexer.front == keyword!"alias") {
			auto var = new ScopeVarDef();
			parseVarDef(lexer, var, lexer.front == keyword!"alias");
			ret.states ~= Replaceable!Statement(var);
		} else {
			auto val = parseExpression(lexer);
			if (lexer.front == operator!"}") {
				ret.last = val;
				lexer.popFront;
				return ret;
			} else if (lexer.front == operator!"=") {
				lexer.popFront;
				auto assigner = parseExpression(lexer);
				auto assign = new Assign;
				assign.left = val;
				assign.right = assigner;
				ret.states ~= Replaceable!Statement(assign);
			} else {
				ret.states ~= Replaceable!Statement(val);
			}
		}
		lexer.front.expect(operator!";");
		lexer.popFront;
	}
}

alias parseVarDef = parseWrap!parseVarDefImpl;
VarDef parseVarDefImpl(ref Lexer lexer, VarDef var, bool manifest) {
	var.manifest = manifest;
	lexer.popFront;
	auto type = parseExpression(lexer);
	if (lexer.front != operator!"=") {
		lexer.front.expectType!Identifier;
		var.name = lexer.front.get!(Identifier).value;
		lexer.popFront;
		lexer.front.expect(operator!"=");
		lexer.popFront;
		var.explicitType = type;
	} else {
		assert(lexer.front == operator!"=");
		auto expr = cast(Variable) type;
		if (!expr) {
			error("expected identifier", lexer.front.position);
		}
		var.name = expr.name;
		lexer.popFront;
	}

	var.definition = parseExpression(lexer);
	return var;
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
void parseModule(ref Lexer lexer, Module ret) {
	Modifier globalModifiers;
	while (true) {
		if (lexer.front == Eof()) {
			lexer.popFront;
			return;
		}
		int[] modifiersList;
		while (true) {
			if (lexer.front == keyword!"public") {
				modifiersList ~= indexModifier!"public";
			} else if (lexer.front == keyword!"private") {
				modifiersList ~= indexModifier!"private";
			} else {
				break;
			}
			lexer.popFront;
		}
		if (modifiersList.length > 0 && lexer.front == operator!":") {
			applyModifiers(modifiersList, globalModifiers);
			lexer.popFront;
		} else if (lexer.front == keyword!"let" || lexer.front == keyword!"alias") {
			Modifier localModifiers = globalModifiers;
			applyModifiers(modifiersList, localModifiers);
			auto var = new ModuleVarDef();
			var.modifier = localModifiers;
			parseVarDef(lexer, var, lexer.front == keyword!"alias");
			ret.symbols[var.name] = var;
			if (auto ext = cast(ExternJs) var.definition) {
				if (var.manifest) {
					ext.name = var.name;
				}
			}
			if (auto func = cast(FuncLit) var.definition) {
				func.name = var.name;
			}
			lexer.front.expect(operator!";");
			lexer.popFront;
		} else {
			error("Expected variable or modifiers list", lexer.front.position);
		}
	}
}
