/+
	Copyright (C) 2020  Freddy Angel Cubas "Superstar64"
	This file is part of Aith.

	Aith is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation version 3 of the License.

	Aith is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with Aith.  If not, see <http://www.gnu.org/licenses/>.
+/
module parser.parser;

import std.algorithm;
import std.bigint;
import std.meta;
import std.utf;
import std.conv;

import Lex = lexer;
import lexer : Lexer, Keyword, Operator, operator, keyword;
import parser.ast;
import parser.astimpl;
import app : readParserModule;

import misc.position;

Module parseModule(ref Lexer lexer) {
	auto ret = new Module;
	while (true) {
		if (lexer.front == Lex.Eof()) {
			lexer.popFront;
			return ret;
		}
		auto positionStart = lexer.front.position;
		Expression explicitType;
		if (lexer.front == operator!"~") {
			lexer.popFront;
			explicitType = parseExpression(lexer);
			lexer.parseToken!(Operator!"~");
		}
		BindingSort sort;
		if (lexer.front == keyword!"symbol") {
			sort = BindingSort.symbol;
			lexer.popFront;
		} else if (lexer.front == keyword!"template") {
			sort = BindingSort.generative;
			lexer.popFront;
		} else if (lexer.front == keyword!"inline") {
			sort = BindingSort.inline;
			lexer.popFront;
		} else if (lexer.front == keyword!"overload") {
			sort = BindingSort.overload;
			lexer.popFront;
		} else {
			error("Expected symbol qualifier", lexer.front.position);
		}
		auto name = lexer.parseToken!(Lex.Identifier);
		string classTypeVariable;
		Expression classTypeScheme;
		if (sort == BindingSort.overload) {
			lexer.parseToken!(Operator!"{");
			lexer.parseToken!(Operator!"<");
			classTypeVariable = lexer.parseToken!(Lex.Identifier);
			lexer.parseToken!(Operator!">");
			classTypeScheme = lexer.parseExpression;
			lexer.parseToken!(Operator!"}");
		}
		lexer.parseToken!(Operator!"=");

		auto value = parseExpression(lexer);
		auto position = positionStart.join(lexer.front.position);
		ret.bindings ~= make!ModuleBinding(position, name, sort, explicitType, classTypeVariable, classTypeScheme, value);
		lexer.parseToken!(Operator!";");
	}
	assert(0);
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
	return parseBinary!("->", "~>", "|||", parseBinary!("&&", "||", parseBinary!("==", "!=", "<=", ">=", "<", ">", parseBinary!("+", "-", parseBinary!("*", "/", "%", parsePrefix!("-", "*", "!"))))))(lexer);
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
	auto value = dispatchLexerFailable!(parseCoreDispatch, Operator!"(&", Lex.IntLiteral, Lex.CharLiteral, Operator!"(", Lex.Identifier, Keyword!"if", Keyword!"import", Lex.StringLiteral, Operator!"[", Keyword!"extern", Operator!"<", Keyword!"has", Operator!"|", Keyword!"raw", Keyword!"unique", Keyword!"do", Keyword!"try", Keyword!"run", Operator!"~", Keyword!"require", Keyword!"instance")(null, lexer);
	if (value) {
		return value;
	}

	error("Expected expression", lexer.front.position);
	assert(0);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"do", ref Lexer lexer) {
	if (lexer.front == operator!"=>") {
		lexer.popFront;
		auto internal = lexer.parseExpression;
		return position => make!Do(position, internal);
	} else {
		lexer.parseToken!(Operator!"{");
		auto internal = lexer.parseExpression;
		lexer.parseToken!(Operator!"}");
		return position => make!Do(position, internal);
	}
}

Expression delegate(Position) parseCoreDispatch(Keyword!"try", ref Lexer lexer) {
	if (lexer.front == operator!"=>") {
		lexer.popFront;
		auto internal = lexer.parseExpression;
		return position => make!Try(position, internal);
	} else {
		lexer.parseToken!(Operator!"{");
		auto internal = lexer.parseExpression;
		lexer.parseToken!(Operator!"}");
		return position => make!Try(position, internal);
	}
}

Expression delegate(Position) parseCoreDispatch(Keyword!"run", ref Lexer lexer) {
	auto value = lexer.parseExpression;
	lexer.parseToken!(Operator!";");
	auto last = lexer.parseExpression;
	return position => make!Run(position, value, last);
}

Expression delegate(Position) parseCoreDispatch(Operator!"~", ref Lexer lexer) {
	bool shadow;
	Lex.Identifier name;
	if (lexer.front == operator!"|") {
		lexer.popFront;
		name = lexer.parseToken!(Lex.Identifier);
		lexer.parseToken!(Operator!"|");
		shadow = true;
	} else {
		name = lexer.parseToken!(Lex.Identifier);
	}
	if (lexer.front == operator!"=>") {
		lexer.popFront;
		auto text = lexer.parseExpression;
		return position => make!MacroFunctionLiteral(position, text, name, shadow);
	} else {
		lexer.parseToken!(Operator!"{");
		auto text = lexer.parseExpression;
		lexer.parseToken!(Operator!"}");
		return position => make!MacroFunctionLiteral(position, text, name, shadow);
	}
}

Expression[] parseExtendsList(ref Lexer lexer) {
	Expression[] constraints;
	while (true) {
		constraints ~= lexer.parseCore;
		if (lexer.front != operator!"&") {
			break;
		}
		lexer.popFront;
	}
	return constraints;
}

Expression delegate(Position) parseCoreDispatch(string word)(Keyword!word, ref Lexer lexer) if (word == "raw" || word == "unique") {
	auto value = lexer.parseCore;
	if (lexer.front == operator!"*") {
		lexer.popFront;
		return position => make!(TypePointer!word)(position, value);
	} else if (lexer.front == operator!"[") {
		lexer.popFront;
		lexer.parseToken!(Operator!"]");
		return position => make!(TypeArray!word)(position, value);
	}
	error("Expected pointer or array", lexer.front.position);
	assert(0);
}

Expression delegate(Position) parseCoreDispatch(Operator!"<", ref Lexer lexer) {
	ForallBinding[] bindings;
	while (true) {
		auto name = lexer.parseToken!(Lex.Identifier).value;
		Expression[] constraints;
		if (lexer.front == keyword!"extends") {
			lexer.popFront;
			constraints = lexer.parseExtendsList;
		}
		bindings ~= ForallBinding(name, constraints);
		if (lexer.front == operator!">") {
			break;
		}
		lexer.parseToken!(Operator!",");
	}
	lexer.popFront;
	auto value = lexer.parseExpression;
	return position => make!Forall(position, bindings, value);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"has", ref Lexer lexer) {
	auto index = lexer.parseToken!(Lex.IntLiteral).toInt;
	lexer.parseToken!(Operator!":");
	auto type = lexer.parseCore;
	return position => make!ConstraintTuple(position, index, type);
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

Expression delegate(Position) parseCoreDispatch(Lex.IntLiteral value, ref Lexer lexer) {
	return position => make!IntLit(position, value);
}

Expression delegate(Position) parseCoreDispatch(Lex.CharLiteral value, ref Lexer lexer) {
	auto code = decodeFront(value.value);
	if (value.value.length != 0) {
		error("Char Lit to big", lexer.front.position);
	}
	return position => make!CharLit(position, code);
}

T[] parseListImpl(T, alias parser, alias op = operator!",")(ref Lexer lexer) {
	T[] result;
	while (true) {
		result ~= parser(lexer);
		if (lexer.front != op) {
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

Expression delegate(Position) parseCoreDispatch(Lex.Identifier identifier, ref Lexer lexer) {
	return position => make!Variable(position, identifier.value, false);
}

Expression delegate(Position) parseCoreDispatch(Operator!"|", ref Lexer lexer) {
	auto identifier = lexer.parseToken!(Lex.Identifier);
	lexer.parseToken!(Operator!"|");
	return position => make!Variable(position, identifier.value, true);
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

Expression delegate(Position) parseCoreDispatch(Keyword!"import", ref Lexer lexer) {
	auto file = lexer.parseToken!(Lex.StringLiteral).value;
	auto value = () => readParserModule(file);
	return position => make!Import(position, value);
}

Expression delegate(Position) parseCoreDispatch(Lex.StringLiteral value, ref Lexer lexer) {
	return position => make!StringLit(position, value.value);
}

Expression delegate(Position) parseCoreDispatch(Operator!"[", ref Lexer lexer) {
	auto values = parseList(lexer);
	lexer.parseToken!(Operator!"]");
	return position => make!ArrayLit(position, values);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"extern", ref Lexer lexer) {
	auto name = lexer.parseToken!(Lex.StringLiteral).value;
	auto scheme = lexer.parseExpression;
	return position => make!ExternJs(position, name, scheme);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"require", ref Lexer lexer) {
	auto value = lexer.parseCore;
	return position => make!Requirement(position, value);
}

Expression delegate(Position) parseCoreDispatch(Keyword!"instance", ref Lexer lexer) {
	lexer.parseToken!(Operator!"(");
	auto type = lexer.parseExpression;
	lexer.parseToken!(Operator!")");
	lexer.parseToken!(Operator!"{");
	auto term = lexer.parseExpression;
	lexer.parseToken!(Operator!"}");
	return position => make!Instance(position, type, term);
}

Expression parsePostfix(ref Lexer lexer, Expression current) {
	auto position = lexer.front.position;
	return dispatchLexerFailable!(parsePostfixDispatch, Operator!".", Operator!"[", Operator!"&[", Operator!"(", Operator!"::", Operator!"_", Operator!":", Operator!"&*_", Operator!"=>", Operator!"{", Operator!"=", Operator!"<-", Operator!"`")(current, lexer, current, position);
}

Expression parsePostfixDispatch(T)(T operator, ref Lexer lexer, Expression current, Position postfixStart) {
	auto result = parsePostfixDispatchImpl(operator, lexer, current, postfixStart);
	auto position = current.position.join(lexer.front.position);
	return parsePostfix(lexer, result(position));
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"_", ref Lexer lexer, Expression current, Position postfixStart) {
	auto index = lexer.parseToken!(Lex.IntLiteral)
		.to!uint;
	return position => make!TupleIndex(position, current, index);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"&*_", ref Lexer lexer, Expression current, Position postfixStart) {
	auto index = lexer.parseToken!(Lex.IntLiteral)
		.to!uint;
	return position => make!TupleIndexAddress(position, current, index);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"=>", ref Lexer lexer, Expression current, Position postfixStart) {
	auto pattern = current.patternMatch;
	auto text = parseExpression(lexer);
	return position => make!FunctionLiteral(position, text, pattern);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"(", ref Lexer lexer, Expression current, Position postfixStart) {
	auto argument = parseTupleEnd!(operator!")")(lexer);
	lexer.popFront;
	return position => make!Call(position, current, argument(postfixStart.join(lexer.front.position)));
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"{", ref Lexer lexer, Expression current, Position postfixStart) {
	auto pattern = current.patternMatch;
	auto text = parseExpression(lexer);
	lexer.parseToken!(Operator!"}");
	return position => make!FunctionLiteral(position, text, pattern);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"::", ref Lexer lexer, Expression current, Position postfixStart) {
	lexer.expectType!(Lex.Identifier);
	auto index = lexer.parseToken!(Lex.Identifier).value;
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
	auto argument = lexer.parseExpression;
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

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"=", ref Lexer lexer, Expression current, Position) {
	auto pattern = current.patternMatch();
	auto value = parseExpression(lexer);
	lexer.parseToken!(Operator!";");
	auto last = parseExpression(lexer);
	return position => make!VariableDefinition(position, pattern, value, last);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"<-", ref Lexer lexer, Expression current, Position) {
	auto argument = lexer.parseExpression;
	return position => make!(Binary!"<-")(position, current, argument);
}

Expression delegate(Position) parsePostfixDispatchImpl(Operator!"`", ref Lexer lexer, Expression current, Position) {
	return position => make!FromRuntime(position, current);
}
