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
module parser.parser;

import std.bigint;
import std.meta;
import std.utf;
import std.conv;
import misc;

import parser.ast;
import parser.astimpl;
import app;
import lexer;
import std.algorithm;

//todo this is ugly fix it
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
		} else {
			Modifier localModifiers = globalModifiers;
			applyModifiers(modifiersList, localModifiers);
			auto var = make!ModuleVarDef();
			var.modifier = localModifiers;
			parseVarDef(lexer, var);
			ret.symbols ~= var;
			lexer.expect(operator!";");
			lexer.popFront;
		}
	}
}

private:

alias parseVarDef = parseWrap!parseVarDefImpl;
ModuleVarDef parseVarDefImpl(ref Lexer lexer, ModuleVarDef var) {
	var.name = lexer.expectType!Identifier;
	lexer.popFront;
	if (lexer.front == operator!":") {
		lexer.popFront;
		var.explicitType = parseExpression(lexer);
	}
	lexer.expect(operator!"=");
	lexer.popFront;

	var.value = parseExpression(lexer);
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

template dispatchLexer(alias fun, Types...) {
	auto dispatchLexer(T...)(ref Lexer lexer, T args) {
		foreach (Type; Types) {
			if (lexer.front.peek!Type) {
				auto token = lexer.front.get!Type;
				lexer.popFront;
				return fun(token, lexer, args);
			}
		}
		assert(0, T.stringof);
	}
}

template dispatchLexerFailable(alias fun, Types...) {
	auto dispatchLexerFailable(Fail, T...)(Fail fail, ref Lexer lexer, T args) {
		foreach (Type; Types) {
			if (lexer.front.peek!Type) {
				auto token = lexer.front.get!Type;
				lexer.popFront;
				return fun(token, lexer, args);
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
	return parseBinary!("->", parseBinary!("&&", "||", parseBinary!("==", "!=", "<=", ">=", "<", ">", parseBinary!("+", "-", "~", parseBinary!("*", "/", "%", parsePrefix!("-", "*", "!"))))))(lexer);
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
			auto ret = make!(Binary!o);
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
			auto ret = make!(Prefix!o);
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
	auto value = dispatchLexerFailable!(parseCoreDispatch, Operator!"(&", Keyword!"integer", Keyword!"natural", Keyword!"character", Keyword!"boolean", IntLiteral, Keyword!"true", Keyword!"false", CharLiteral, Keyword!"cast", Operator!"(", Identifier, Keyword!"if", Keyword!"while", Keyword!"new", Keyword!"import", StringLiteral, Operator!"[", Keyword!"extern", Operator!"{", Keyword!"length")(null, lexer);
	if (value) {
		return value;
	}

	error("Expected expression", lexer.front.position);
	assert(0);
}

Expression parseCoreDispatch(Operator!"(&", ref Lexer lexer) {
	if (lexer.front == operator!"&)") {
		lexer.popFront;
		return make!TypeTuple;
	}
	auto values = parseList(lexer);
	lexer.expect(operator!"&)");
	lexer.popFront;
	auto result = make!TypeTuple;
	result.values = values;
	return result;
}

auto parseToken(T)(ref Lexer lexer) {
	auto result = lexer.expectType!T;
	lexer.popFront;
	return result;
}

Expression parseCoreDispatch(Keyword!"integer", ref Lexer lexer) {
	auto integer = make!TypeInt;
	integer.size = parseToken!IntLiteral(lexer).toInt;
	integer.signed = true;
	return integer;

}

Expression parseCoreDispatch(Keyword!"natural", ref Lexer lexer) {
	auto natural = make!TypeInt();
	natural.size = parseToken!IntLiteral(lexer).toInt;
	natural.signed = false;
	return natural;
}

Expression parseCoreDispatch(Keyword!"character", ref Lexer lexer) {
	return make!TypeChar();
}

Expression parseCoreDispatch(Keyword!"boolean", ref Lexer lexer) {
	return make!TypeBool();
}

Expression parseCoreDispatch(IntLiteral value, ref Lexer lexer) {
	auto ret = make!IntLit;
	ret.value = value;
	return ret;
}

Expression parseCoreDispatch(Keyword!"true", ref Lexer lexer) {
	auto ret = make!BoolLit();
	ret.yes = true;
	return ret;
}

Expression parseCoreDispatch(Keyword!"false", ref Lexer lexer) {
	auto ret = make!BoolLit();
	ret.yes = false;
	return ret;
}

Expression parseCoreDispatch(CharLiteral value, ref Lexer lexer) {
	auto ret = make!CharLit();
	ret.value = decodeFront(value.value);
	if (value.value.length != 0) {
		error("TypeChar Lit to big", lexer.front.position);
	}
	return ret;
}

Expression parseCoreDispatch(Keyword!"cast", ref Lexer lexer) {
	auto ret = make!Cast();
	ret.type = parseCore(lexer);
	ret.value = parseExpression(lexer);
	return ret;
}

T[] parseListImpl(T, alias parser)(ref Lexer lexer) {
	T[] result;
	while (true) {
		result ~= parseExpression(lexer);
		if (lexer.front != operator!",") {
			break;
		}
		lexer.popFront;
	}
	return result;
}

Expression[] parseList(ref Lexer lexer) {
	return parseListImpl!(Expression, parseExpression)(lexer);
}

Expression parseCoreDispatch(End...)(Operator!"(", ref Lexer lexer) {
	auto result = parseTupleEnd!(operator!")")(lexer);
	lexer.popFront;
	return result;
}

Expression parseTupleEnd(End...)(ref Lexer lexer) {
	foreach (stop; End) {
		if (lexer.front == stop) {
			auto ret = make!TupleLit();
			return ret;
		}
	}
	auto list = parseList(lexer);
	lexer.expect(End);
	if (list.length == 1) {
		return list[0];
	} else {
		auto result = make!TupleLit();
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

Expression parseCoreDispatch(Identifier identifier, ref Lexer lexer) {
	auto ret = make!Variable();
	ret.name = identifier.value;
	return ret;
}

Expression parseCoreDispatch(Keyword!"if", ref Lexer lexer) {
	auto ret = make!If();
	ret.cond = parseExpression(lexer);
	lexer.expect(keyword!"then");
	lexer.popFront;
	ret.yes = parseExpression(lexer);
	if (lexer.front == keyword!"else") {
		lexer.popFront;
		ret.no = parseExpression(lexer);
	} else {
		ret.no = make!TupleLit();
	}
	return ret;
}

Expression parseCoreDispatch(Keyword!"while", ref Lexer lexer) {
	auto ret = make!While();
	ret.cond = parseExpression(lexer);
	if (lexer.front == keyword!"then") {
		lexer.popFront;
		ret.state = parseExpression(lexer);
	} else {
		ret.state = make!TupleLit();
	}
	return ret;
}

Expression parseCoreDispatch(Keyword!"new", ref Lexer lexer) {
	if (lexer.front == operator!"[") {
		auto ret = make!NewArray();
		ret.length = parseTuple!(operator!"[", operator!"]")(lexer);
		assert(ret.length);
		ret.value = parseExpression(lexer);
		return ret;
	} else {
		auto ret = make!New();
		ret.value = parseExpression(lexer);
		return ret;
	}
}

Expression parseCoreDispatch(Keyword!"import", ref Lexer lexer) {
	auto ret = make!Import();
	lexer.expectType!StringLiteral;
	auto file = lexer.front.get!StringLiteral.value;
	lexer.popFront();
	ret.mod = findAndReadModule(file);
	return ret;
}

alias parsePattern = parseWrap!parsePatternImpl;

Pattern parsePatternImpl(ref Lexer lexer) {
	auto value = dispatchLexerFailable!(parsePatternDispatch, Operator!"(", Identifier)(null, lexer);
	if (value) {
		return value;
	}

	error("Expected pattern", lexer.front.position);
	assert(0);
}

Pattern parsePatternDispatch(Identifier name, ref Lexer lexer) {
	auto ret = make!NamedArgument();
	ret.name = name;
	return ret;
}

Pattern parsePatternDispatch(Operator!"(", ref Lexer lexer) {
	Pattern[] matches;
	if (lexer.front == operator!")") {
		lexer.popFront;
		auto ret = make!TupleArgument();
		ret.matches = matches;
		return ret;
	}
	matches ~= parsePattern(lexer);
	while (lexer.front == operator!",") {
		lexer.popFront;
		matches ~= parsePattern(lexer);
	}
	lexer.expect(operator!")");
	lexer.popFront;
	if (matches.length == 1) {
		return matches[0];
	} else {
		auto ret = make!TupleArgument();
		ret.matches = matches;
		return ret;
	}
}

Expression parseCoreDispatch(StringLiteral value, ref Lexer lexer) {
	auto ret = make!StringLit;
	ret.value = value.value;
	return ret;
}

Expression parseCoreDispatch(Operator!"[", ref Lexer lexer) {
	auto values = parseList(lexer);
	lexer.expect(operator!"]");
	lexer.popFront;
	auto ret = make!ArrayLit;
	ret.values = values;
	return ret;
}

Expression parseCoreDispatch(Keyword!"extern", ref Lexer lexer) {
	auto ret = make!ExternJs;
	ret.name = lexer.expectType!StringLiteral;
	lexer.popFront;
	return ret;
}

Expression parseCoreDispatch(Keyword!"length", ref Lexer lexer) {
	return make!Length;
}

Expression parsePostfix(ref Lexer lexer, Expression current) {
	auto position = lexer.front.position;
	return dispatchLexerFailable!(parsePostfixDispatch, Operator!".", Operator!"[", Operator!"(", Operator!"(*)", Operator!"[*]", Operator!"::", Operator!"_", Operator!":", Operator!"&[", Operator!"&*_", Operator!"=>")(current, lexer, current, position);
}

Expression parsePostfixDispatch(T)(T operator, ref Lexer lexer, Expression current, Position postfixStart) {
	auto result = parsePostfixDispatchImpl(operator, lexer, current, postfixStart);
	result.position = current.position.join(lexer.front.position);
	return parsePostfix(lexer, result);
}

Expression parsePostfixDispatchImpl(Operator!"_", ref Lexer lexer, Expression current, Position postfixStart) {
	auto ret = make!TupleIndex();
	ret.tuple = current;
	ret.index = lexer.expectType!IntLiteral
		.to!uint;
	lexer.popFront;
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"&*_", ref Lexer lexer, Expression current, Position postfixStart) {
	auto ret = make!TupleIndexAddress();
	ret.tuple = current;
	ret.index = lexer.expectType!IntLiteral
		.to!uint;
	lexer.popFront;
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"=>", ref Lexer lexer, Expression current, Position postfixStart) {
	auto ret = make!FuncLit;
	auto pattern = current.patternMatch;
	if (pattern is null) {
		error("expected pattern match", current.position);
	}
	ret.argument = pattern;
	ret.text = parseExpression(lexer);
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"::", ref Lexer lexer, Expression current, Position postfixStart) {
	auto ret = make!UseSymbol();
	ret.value = current;
	lexer.expectType!(Identifier);
	ret.index = lexer.front.get!(Identifier).value;
	lexer.popFront;
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!".", ref Lexer lexer, Expression current, Position postfixStart) {
	auto ret = make!Call;
	auto lambda = parseCore(lexer);
	ret.calle = lambda;
	ret.argument = current;
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!":", ref Lexer lexer, Expression current, Position postfixStart) {
	auto ret = make!Infer();
	ret.value = current;
	ret.type = parseExpression(lexer);
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"&[", ref Lexer lexer, Expression current, Position postfixStart) {
	auto argument = parseExpression(lexer);
	lexer.expect(operator!"]");
	lexer.popFront;
	auto ret = make!IndexAddress;
	ret.array = current;
	ret.index = argument;
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"[", ref Lexer lexer, Expression current, Position postfixStart) {
	auto argument = parseTupleEnd!(operator!"]", operator!"..")(lexer);
	return dispatchLexer!(parsePostfixBraceDispatch, Operator!"]", Operator!"..")(lexer, current, argument, postfixStart);
}

Expression parsePostfixBraceDispatch(Operator!"..", ref Lexer lexer, Expression current, Expression argument, Position postfixStart) {
	auto ret = make!Slice;
	ret.array = current;
	ret.left = argument;
	ret.left.position = postfixStart.join(lexer.front.position);
	ret.right = parseTupleEnd!(operator!"]")(lexer);
	lexer.popFront;
	ret.right.position = postfixStart.join(lexer.front.position);
	return ret;
}

Expression parsePostfixBraceDispatch(Operator!"]", ref Lexer lexer, Expression current, Expression argument, Position postfixStart) {
	auto ret = make!Index;
	ret.array = current;
	ret.index = argument;
	ret.index.position = postfixStart.join(lexer.front.position);
	return ret;
}

Expression parsePostfixDispatchImpl(Operator!"(", ref Lexer lexer, Expression current, Position postfixStart) {
	auto argument = parseTupleEnd!(operator!")")(lexer);
	assert(lexer.front == operator!")");
	lexer.popFront;
	auto ret = make!Call();
	ret.calle = current;
	ret.argument = argument;
	argument.position = postfixStart.join(lexer.front.position);
	return ret;
}

Expression parsePostfixDispatchImpl(string op)(Operator!op, ref Lexer lexer, Expression current, Position) if (op == "(*)" || op == "[*]") {
	auto ret = make!(Postfix!op)();
	ret.value = current;
	return ret;
}

Expression parseCoreDispatch(Operator!"{", ref Lexer lexer) {
	auto ret = make!Scope();
	//todo handle position for these
	while (true) {
		if (lexer.front == operator!"}") {
			lexer.popFront;
			return ret;
		}
		auto val = parseExpression(lexer);
		if (lexer.front == operator!"}") {
			ret.last = val;
			lexer.popFront;
			return ret;
		} else if (lexer.front == operator!"<-") {
			lexer.popFront;
			auto assigner = parseExpression(lexer);
			auto assign = make!Assign;
			assign.left = val;
			assign.right = assigner;
			ret.states ~= assign;
		} else if (lexer.front == operator!"=") {
			lexer.popFront;
			auto variabledef = make!VariableDef();
			auto pattern = val.patternMatch();
			if (pattern is null) {
				error("expected pattern match", pattern.position);
			}
			auto expression = lexer.parseExpression;
			variabledef.variable = pattern;
			variabledef.value = expression;
			ret.states ~= variabledef;
		} else {
			ret.states ~= val;
		}

		lexer.expect(operator!";");
		lexer.popFront;
	}
}
