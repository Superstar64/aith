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
module lexer;
import std.algorithm;
import std.ascii;
import std.bigint;
import std.conv;
import std.typecons;
import std.variant;
import std.range;
import std.array;
import std.meta;
import std.utf;

import misc;

@property {
	char front(string str) {
		return str[0];
	}

	void popFront(ref string str) {
		str = str[1 .. $];
	}

	void popFrontN(ref string str, size_t n) {
		str = str[n .. $];
	}

	bool empty(string str) {
		return str.length == 0;
	}

	string next(ref string str) {
		return str.nextN(1);
	}

	string nextN(ref string str, size_t length) {
		auto result = str[0 .. length];
		str.popFrontN(length);
		return result;
	}
}

enum keywords = AliasSeq!("alias", "let", "boolean", "cast", "character", "else", "extern",
			"false", "if", "import", "infer", "integer", "new", "of",
			"private", "public", "tuple", "then", "true", "natural", "while");
struct Keyword(string keyword) if (staticIndexOf!(keyword, keywords) >= 0) {
	string toString() {
		return keyword;
	}
}

auto keyword(string key)() {
	return Keyword!key();
}

//must be sorted according to string length
enum operators = AliasSeq!("[*]", "(*)", ":::", "==", "!=", "<=", ">=", "&&",
			"||", "::", "$@", "->", "..", "<", ">", "+", "-", "*", "/", "%",
			"=", "!", "~", "&", "|", "^", ":", "$", "@", "{", "}", "(", ")",
			"[", "]", ".", ",", ";", "_");

struct Operator(string operator) if (staticIndexOf!(operator, operators) >= 0) {
	string toString() {
		return operator;
	}
}

auto operator(string oper)() {
	return Operator!oper();
}

template parseOperatorTemplate(string op) {
	Nullable!(Operator!op) parseOperator(ref string file, Position) {
		if (file.startsWith(op)) {
			file.popFrontN(op.length);
			return typeof(return)(Operator!op());
		}
		return typeof(return).init;
	}
}

struct Identifier {
	string value;
	alias value this;
	string toString() {
		return value;
	}
}

Nullable!Identifier parseIdentifier(ref string file, Position) {
	if (file.front.isAlpha) {
		auto length = file[].until!(a => !(a.isAlphaNum)).count;
		return typeof(return)(Identifier(file.nextN(length)));
	}
	return typeof(return).init;
}

struct IntLiteral {
	BigInt value;
	alias value this;
	string toString() {
		return value.to!string;
	}
}

Nullable!IntLiteral parseIntLiteral(ref string file, Position) {
	if (file.front.isDigit) {
		auto length = file[].until!(a => !a.isDigit).count;
		return typeof(return)(IntLiteral(BigInt(file.nextN(length))));
	}
	return typeof(return).init;
}

string readStringWithEscapes(ref string file, char end, string current, out string err) {
	enum errEoF = "Unexpected eof when parsing string";
	enum validHex = "0123456789abcdefABCDEF";

	enum escapeMap = [
			'a' : '\a', 'b' : '\b', 'f' : '\f', 'n' : '\n', 'r' : '\r', 't' : '\t',
			'v' : '\v', '\\' : '\\', '\'' : '\'', '"' : '"', '`' : '`', '0' : '\0'
		];
	while (true) {
		auto length = file[].until!(a => a == '\\' || a == end)
			.tee!(a => current ~= a)
			.count;
		file.popFrontN(length);
		if (file.empty) {
			err = errEoF;
			return "";
		}
		if (file.front in escapeMap) {
			current ~= escapeMap[file.front];
		} else if (file.front == '-') {
			assert(0, "todo implement \\-HEX-/ literals");
		} else if (file.front == end) {
			return current;
		}
	}
}

string readString(ref string file, char start, char end, out string err) {
	if (file.front != start) {
		return null;
	}
	file.popFront;
	auto length = file[].until!(a => a == '\\' || a == end).count;
	auto str = file.nextN(length);
	if (file.empty || file.front == '\\') {
		return readStringWithEscapes(file, end, str, err);
	}
	file.popFront;
	return str;
}

Nullable!T parseStringLiteral(T)(ref string file, Position position) {
	string err;
	auto str = readString(file, T.charCode, T.charCode, err);
	if (err) {
		error(err, position);
	}
	if (str) {
		return typeof(return)(T(str));
	}
	return typeof(return).init;
}

struct CharLiteral {
	string value;
	alias value this;
	enum charCode = '\'';
}

struct StringLiteral {
	string value;
	alias value this;
	enum charCode = '"';
}

struct Eof {
}

Nullable!Eof parseEOF(ref string file, Position) {
	if (file.length == 0) {
		return typeof(return)(Eof());
	}
	return typeof(return).init;
}

struct Token {
	Position position;
	Algebraic!(Identifier, IntLiteral, CharLiteral, StringLiteral,
			staticMap!(Operator, operators), staticMap!(Keyword, keywords), Eof) value;
	alias value this;

	bool opEquals(T)(T t) if (!is(T == Token)) {
		return value == t;
	}

	auto expect(T...)(T expected) if (T.length == 1) {
		if (this != expected) {
			error("Expected " ~ expected.to!string, position);
		}
	}

	auto expect(T...)(T expectedList) if (T.length != 1) {
		foreach (expected; expectedList) {
			if (this == expected) {
				return;
			}
		}
		error("Expected " ~ T.stringof, position);
	}

	auto expectType(T)() {
		if (auto wanted = value.peek!T) {
			return *wanted;
		}
		error("Expected " ~ T.stringof, position);
		assert(0);
	}
}

void removeMultiLine(ref string file) {
	while (!file.startsWith("/#")) {
		if (file.startsWith("#/")) {
			file.popFrontN(2);
			removeMultiLine(file);
		}
		if (file.empty) {
			return;
		}
		file.popFront;
	}
	file.popFrontN(2);
}

void removeSingleLine(ref string file) {
	if (file.startsWith('\n')) {
		file.popFront;
		return;
	}
	if (file.empty) {
		return;
	}
	file.popFront;
	file.removeSingleLine;
}

void removeComments(ref string file) {
	if (file.empty) {
		return;
	}
	if (file.front.isWhite) {
		file.popFront;
		file.removeComments;
	}
	if (file.startsWith("#/")) {
		file.popFrontN(2);
		file.removeMultiLine;
		file.removeComments;
	}
	if (file.startsWith("#")) {
		file.removeSingleLine;
		file.removeComments;
	}
}

template metaParseDot(alias T) {
	alias metaParseDot = T.parseOperator;
}

alias Parsers = AliasSeq!(parseEOF, parseIdentifier, parseIntLiteral, parseStringLiteral!CharLiteral,
		parseStringLiteral!StringLiteral, staticMap!(metaParseDot,
			staticMap!(parseOperatorTemplate, operators)));

struct Lexer {
	string fileName;
	uint currentLine = 1;
	uint currentIndex;
	string file;

	string fileOriginal;
	Token head;
	Token lookAhead;
	Token front() {
		return head;
	}

	this(string fileName, string file) {
		this.fileName = fileName;
		this.file = file;
		this.fileOriginal = file;
		popFront;
		popFront;
	}

	void countLines(string old) {
		currentIndex += old.length - file.length;
		currentLine += old[0 .. old.length - file.length].filter!(a => a == '\n').count;
	}

	void clean() {
		auto old = file;
		file.removeComments;
		countLines(old);
	}

	void popFront() {
		head = lookAhead;
		getNext();
		if (auto top = head.peek!Identifier) {
			while (lookAhead.peek!Identifier) {
				top.value ~= " " ~ lookAhead.get!Identifier;
				getNext();
			}
		}
	}

	void getNext() {
		clean();
		auto old = file;
		auto position = Position(fileName, currentLine, fileOriginal, currentIndex);
		scope (success) {
			lookAhead.position = position.join(Position(fileName, currentLine,
					fileOriginal, currentIndex));
		}
		foreach (parserFun; Parsers) {
			auto tokenPartNullable = parserFun(file, position);
			if (!tokenPartNullable.isNull) {
				countLines(old);
				auto tokenPart = tokenPartNullable.get();
				static if (is(typeof(tokenPart) == Identifier)) {
					foreach (keyword; keywords) {
						if (tokenPart == keyword) {
							lookAhead.value = typeof(front.value)(Keyword!keyword());
							return;
						}
					}
				}
				lookAhead.value = typeof(front.value)(tokenPart);
				return;
			}
		}

		error("Unknown Token", position);
	}

@property:
	bool empty() {
		return front == Eof();
	}

	auto save() {
		return this;
	}
}
