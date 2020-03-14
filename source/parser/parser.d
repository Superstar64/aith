/+
	Copyright (C) 2020  Freddy Angel Cubas "Superstar64"
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

import parser.ast;
import parser.astimpl;
import app;
import lexer;
import std.algorithm;

import misc.position;

//todo this is ugly fix it
void parseModule(ref Lexer lexer, Module ret) {

	while (true) {
		if (lexer.front == Eof()) {
			lexer.popFront;
			return;
		}
		auto positionStart = lexer.front.position;
		auto name = lexer.parseToken!Identifier;
		Expression explicitType;
		string[] polymorphicVariables;
		if (lexer.front == operator!":") {
			lexer.popFront;
			if (lexer.front == keyword!"forall") {
				lexer.popFront;
				string parseLit(ref Lexer lexer) {
					return lexer.parseToken!Identifier;
				}

				polymorphicVariables = parseListImpl!(string, parseLit)(lexer);
				lexer.expect(operator!".");
				lexer.popFront;
			}
			explicitType = parseExpression(lexer);
			lexer.expect(operator!";");
			lexer.popFront;
			auto duplicate = lexer.parseToken!Identifier;
			if (name != duplicate) {
				error("variable definition name doesn't type definition name", lexer.front.position);
			}
		}
		lexer.parseToken!(Operator!"=");

		auto value = parseExpression(lexer);
		auto position = positionStart.join(lexer.front.position);
		ret.symbols ~= make!ModuleVarDef(position, polymorphicVariables, name, explicitType, value);
		lexer.parseToken!(Operator!";");
	}
}

private:

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
		return value(position.join(lexer.front.position));
	}
}

auto parseToken(T)(ref Lexer lexer) {
	auto result = lexer.expectType!T;
	lexer.popFront;
	return result;
}

Expression parseExpression(ref Lexer lexer) {
	return parseBinary!("->", parseBinary!("&&", "||", parseBinary!("==", "!=", "<=", ">=", "<", ">", parseBinary!("+", "-", "~", parseBinary!("*", "/", "%", parsePrefix!("-", "*", "!"))))))(lexer);
}

Expression parseBinary(args...)(ref Lexer lexer) {
	return parseWrap!(parseBinaryImpl!(args))(lexer);
}

Expression delegate(Position) parseBinaryImpl(args...)(ref Lexer lexer) {
	alias opers = args[0 .. $ - 1];
	alias sub = args[$ - 1];
	auto internal = sub(lexer);
	foreach (o; opers) {
		if (lexer.front == operator!o) {
			lexer.popFront;
			return position => make!(Binary!o)(position, internal, parseBinary!args(lexer));
		}
	}
	return position => internal;
}

Expression parsePrefix(opers...)(ref Lexer lexer) {
	return parseWrap!(parsePrefixImpl!(opers))(lexer);
}

Expression delegate(Position) parsePrefixImpl(opers...)(ref Lexer lexer) {
	foreach (o; opers) {
		if (lexer.front == operator!o) {
			lexer.popFront;
			return position => make!(Prefix!o)(position, parsePrefix!opers(lexer));
		}
	}
	return position => parseWithPostfix(lexer);
}

Expression parseWithPostfix(ref Lexer lexer) {
	return parsePostfix(lexer, parseCore(lexer));
}

alias parseCore = parseWrap!parseCoreImpl;
Expression delegate(Position) parseCoreImpl(ref Lexer lexer) {
	auto value = dispatchLexerFailable!(parseCoreDispatch, Operator!"(&", Keyword!"integer", Keyword!"natural", Keyword!"character", Keyword!"boolean", IntLiteral, Keyword!"true", Keyword!"false", CharLiteral, Keyword!"cast", Operator!"(", Identifier, Keyword!"if", Keyword!"while", Keyword!"new", Keyword!"import", StringLiteral, Operator!"[", Keyword!"extern", Keyword!"length")(null, lexer);
	if (value) {
		return value;
	}

	error("Expected expression", lexer.front.position);
	assert(0);
}

Expression delegate(Position) parseCoreDispatch(Operator!"(&", ref Lexer lexer) {
	if (lexer.front == operator!"&)") {
		lexer.popFront;
		return position => make!TypeTuple(position, null);
	}
	auto values = parseList(lexer);
	lexer.expect(operator!"&)");
	lexer.popFront;
	return position => make!TypeTuple(position, values);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"integer", ref Lexer lexer) {
	auto size = parseToken!IntLiteral(lexer).toInt;
	return position => make!TypeInt(position, size, true);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"natural", ref Lexer lexer) {
	auto size = parseToken!IntLiteral(lexer).toInt;
	return position => make!TypeInt(position, size, false);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"character", ref Lexer lexer) {
	return position => make!TypeChar(position);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"boolean", ref Lexer lexer) {
	return position => make!TypeBool(position);
}

Expression delegate(Position) parseCoreDispatch(IntLiteral value, ref Lexer lexer) {
	return position => make!IntLit(position, value);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"true", ref Lexer lexer) {
	return position => make!BoolLit(position, true);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"false", ref Lexer lexer) {
	return position => make!BoolLit(position, false);
}

Expression delegate(Position) parseCoreDispatch(CharLiteral value, ref Lexer lexer) {
	auto code = decodeFront(value.value);
	if (value.value.length != 0) {
		error("Char Lit to big", lexer.front.position);
	}
	return position => make!CharLit(position, code);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"cast", ref Lexer lexer) {
	auto type = parseCore(lexer);
	auto value = parseExpression(lexer);
	return position => make!Cast(position, type, value);
}

T[] parseListImpl(T, alias parser)(ref Lexer lexer) {
	T[] result;
	while (true) {
		result ~= parser(lexer);
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

Expression delegate(Position) parseCoreDispatch(End...)(Operator!"(", ref Lexer lexer) {
	auto result = parseTupleEnd!(operator!")")(lexer);
	lexer.popFront;
	return result;
}

Expression delegate(Position) parseTupleEnd(End...)(ref Lexer lexer) {
	foreach (stop; End) {
		if (lexer.front == stop) {
			return position => make!TupleLit(position, null);
		}
	}
	auto list = parseList(lexer);
	lexer.expect(End);
	if (list.length == 1) {
		return position => list[0];
	} else {
		return position => make!TupleLit(position, list);
	}
}

Expression delegate(Position) parseCoreDispatch(Identifier identifier, ref Lexer lexer) {
	return position => make!Variable(position, identifier.value);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"if", ref Lexer lexer) {
	auto condition = parseCore(lexer);

	lexer.parseToken!(Operator!"{");

	auto yes = parseExpression(lexer);

	lexer.parseToken!(Operator!"}");
	lexer.parseToken!(Keyword!"else");
	lexer.parseToken!(Operator!"{");

	auto no = parseExpression(lexer);

	lexer.parseToken!(Operator!"}");

	return position => make!If(position, condition, yes, no);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"while", ref Lexer lexer) {
	auto condition = parseCore(lexer);

	lexer.parseToken!(Operator!"{");

	auto state = parseExpression(lexer);

	lexer.parseToken!(Operator!"}");

	return position => make!While(position, condition, state);
}

Expression parseTuple(alias Start, End...)(ref Lexer lexer) {
	return parseWrap!(parseTupleImpl!(Start, End))(lexer);
}

Expression delegate(Position) parseTupleImpl(alias Start, End...)(ref Lexer lexer) {
	assert(lexer.front == Start);
	lexer.popFront;
	auto result = parseTupleEnd!End(lexer);
	lexer.popFront;
	return result;
}

Expression delegate(Position) parseCoreDispatch(Keyword!"new", ref Lexer lexer) {
	if (lexer.front == operator!"[") {
		auto length = parseTuple!(operator!"[", operator!"]")(lexer);
		auto value = parseExpression(lexer);
		return position => make!NewArray(position, length, value);
	} else {
		auto value = parseExpression(lexer);
		return position => make!New(position, value);
	}
}

Expression delegate(Position) parseCoreDispatch(Keyword!"import", ref Lexer lexer) {
	auto file = lexer.parseToken!StringLiteral.value;
	auto mod = findAndReadModule(file);
	return position => make!Import(position, mod);
}

Expression delegate(Position) parseCoreDispatch(StringLiteral value, ref Lexer lexer) {
	return position => make!StringLit(position, value.value);
}

Expression delegate(Position) parseCoreDispatch(Operator!"[", ref Lexer lexer) {
	auto values = parseList(lexer);
	lexer.parseToken!(Operator!"]");
	return position => make!ArrayLit(position, values);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"extern", ref Lexer lexer) {
	auto name = lexer.parseToken!StringLiteral.value;
	return position => make!ExternJs(position, name);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"length", ref Lexer lexer) {
	return position => make!Length(position);
}

Expression parsePostfix(ref Lexer lexer, Expression current) {
	auto position = lexer.front.position;
	return dispatchLexerFailable!(parsePostfixDispatch, Operator!".", Operator!"[", Operator!"(", Operator!"(*)", Operator!"[*]", Operator!"::", Operator!"_", Operator!":", Operator!"&[", Operator!"&*_", Operator!"=>", Operator!"{", Operator!"=", Operator!"<-")(current, lexer, current, position);
}

Expression parsePostfixDispatch(T)(T operator, ref Lexer lexer, Expression current, Position postfixStart) {
	auto result = parsePostfixDispatchImpl(operator, lexer, current, postfixStart);
	auto position = current.position.join(lexer.front.position);
	return parsePostfix(lexer, result(position));
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"_", ref Lexer lexer, Expression current, Position postfixStart) {
	auto index = lexer.parseToken!IntLiteral
		.to!uint;
	return position => make!TupleIndex(position, current, index);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"&*_", ref Lexer lexer, Expression current, Position postfixStart) {
	auto index = lexer.parseToken!IntLiteral
		.to!uint;
	return position => make!TupleIndexAddress(position, current, index);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"=>", ref Lexer lexer, Expression current, Position postfixStart) {
	auto pattern = current.patternMatch;
	if (pattern is null) {
		error("expected pattern match", current.position);
	}
	auto text = parseExpression(lexer);
	return position => make!FuncLit(position, text, pattern);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"{", ref Lexer lexer, Expression current, Position postfixStart) {
	auto pattern = current.patternMatch;
	if (pattern is null) {
		error("expected pattern match", current.position);
	}
	auto text = parseExpression(lexer);
	lexer.parseToken!(Operator!"}");
	return position => make!FuncLit(position, text, pattern);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"::", ref Lexer lexer, Expression current, Position postfixStart) {
	lexer.expectType!(Identifier);
	auto index = lexer.parseToken!Identifier.value;
	return position => make!UseSymbol(position, current, index);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!".", ref Lexer lexer, Expression current, Position postfixStart) {
	auto lambda = parseCore(lexer);
	return position => make!Call(position, lambda, current);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!":", ref Lexer lexer, Expression current, Position postfixStart) {
	auto type = parseExpression(lexer);
	return position => make!Infer(position, type, current);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"&[", ref Lexer lexer, Expression current, Position postfixStart) {
	auto argument = parseExpression(lexer);
	lexer.parseToken!(Operator!"]");
	return position => make!IndexAddress(position, current, argument);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"[", ref Lexer lexer, Expression current, Position postfixStart) {
	auto argument = parseTupleEnd!(operator!"]", operator!"..")(lexer);
	return dispatchLexer!(parsePostfixBraceDispatch, Operator!"]", Operator!"..")(lexer, current, argument, postfixStart);
}

Expression delegate(Position) parsePostfixBraceDispatch(Operator!"..", ref Lexer lexer, Expression current, Expression delegate(Position) argument, Position postfixStart) {
	auto left = argument(postfixStart.join(lexer.front.position));
	auto position = lexer.front.position;
	auto right = parseTupleEnd!(operator!"]")(lexer);
	lexer.popFront;
	return position => make!Slice(position, current, left, right(position.join(lexer.front.position)));
}

Expression delegate(Position) parsePostfixBraceDispatch(Operator!"]", ref Lexer lexer, Expression current, Expression delegate(Position) argument, Position postfixStart) {
	auto index = argument(postfixStart.join(lexer.front.position));
	return position => make!Index(position, current, index);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"(", ref Lexer lexer, Expression current, Position postfixStart) {
	auto argument = parseTupleEnd!(operator!")")(lexer);
	lexer.popFront;
	return position => make!Call(position, current, argument(postfixStart.join(lexer.front.position)));
}

Expression delegate(Position) parsePostfixDispatchImpl(string op)(Operator!op, ref Lexer lexer, Expression current, Position) if (op == "(*)" || op == "[*]") {
	return position => make!(Postfix!op)(position, current);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"=", ref Lexer lexer, Expression current, Position) {
	auto pattern = current.patternMatch();
	if (pattern is null) {
		error("expected pattern match", current.position);
	}
	auto value = parseExpression(lexer);
	lexer.parseToken!(Operator!";");
	auto last = parseExpression(lexer);
	return position => make!VariableDef(position, pattern, value, last);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"<-", ref Lexer lexer, Expression current, Position) {
	auto right = lexer.parseExpression;
	return position => make!Assign(position, current, right);
}
