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

enum keywords = AliasSeq!("global", "static", "let", "boolean", "cast", "character", "else", "extern", "false", "if", "import", "infer", "integer", "length", "new", "of", "private", "public", "tuple", "then", "true", "natural", "while");
struct Keyword(string keyword) if (staticIndexOf!(keyword, keywords) >= 0) {
	string toString() {
		return keyword;
	}
}

auto keyword(string key)() {
	return Keyword!key();
}

//must be sorted according to string length
enum operators = AliasSeq!("[*]", "(*)", ":::", "==", "!=", "<=", ">=", "&&", "||", "::", "->", "..", "&[", "&*_", "<-", "=>", "(&", "&)", "<", ">", "+", "-", "*", "/", "%", "=", "!", "~", "&", "|", "^", ":", "$", "@", "{", "}", "(", ")", "[", "]", ".", ",", ";", "_");

struct Operator(string operator) if (staticIndexOf!(operator, operators) >= 0) {
	string toString() {
		return operator;
	}
}

auto operator(string oper)() {
	return Operator!oper();
}

struct Identifier {
	string value;
	alias value this;
	string toString() {
		return value;
	}
}

struct IntLiteral {
	BigInt value;
	alias value this;
	string toString() {
		return value.to!string;
	}
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

struct Token {
	Position position;
	Algebraic!(Identifier, IntLiteral, CharLiteral, StringLiteral, staticMap!(Operator, operators), staticMap!(Keyword, keywords), Eof) value;
	alias value this;

	bool opEquals(T)(T t) if (!is(T == Token)) {
		return value == t;
	}
}

template parseOperator(string op) {
	Nullable!(Operator!op) parseOperator(ref string file, void delegate(string) error) {
		if (file.startsWith(op)) {
			file.popFrontN(op.length);
			return Operator!op().nullable;
		}
		return typeof(return).init;
	}
}

template parseKeyword(string key) {
	Nullable!(Keyword!key) parseKeyword(ref string file, void delegate(string) error) {
		if (file.startsWith(key)) {
			file.popFrontN(key.length);
			return Keyword!key().nullable;
		}
		return typeof(return).init;
	}
}

Nullable!string parseIdentifierImpl(ref string file) {
	auto original = file;
	if (file.front.isAlpha) {
		auto length = file[].until!(a => !(a.isAlphaNum)).count;
		auto identifier = file.nextN(length);
		if ([keywords].any!(a => a == identifier)) {
			file = original;
		} else {
			return identifier.nullable;
		}
	}
	return typeof(return).init;
}

Nullable!Identifier parseIdentifier(ref string file, void delegate(string) error) {
	auto identifier = parseIdentifierImpl(file);
	if (!identifier.isNull) {
		auto result = identifier.get;
		while (true) {
			auto original = file;
			file.removeComments;
			auto next = parseIdentifierImpl(file);
			if (next.isNull) {
				file = original;
				return Identifier(result).nullable;
			} else {
				result ~= " " ~ next.get;
			}
		}
	}
	return typeof(return).init;
}

Nullable!IntLiteral parseIntLiteral(ref string file, void delegate(string) error) {
	if (file.front.isDigit) {
		auto length = file[].until!(a => !a.isDigit).count;
		return IntLiteral(BigInt(file.nextN(length))).nullable;
	}
	return typeof(return).init;
}

string readStringWithEscapes(ref string file, char end, string current, out string err) {
	enum errEoF = "Unexpected eof when parsing string";
	enum validHex = "0123456789abcdefABCDEF";

	enum escapeMap = ['a' : '\a', 'b' : '\b', 'f' : '\f', 'n' : '\n', 'r' : '\r', 't' : '\t', 'v' : '\v', '\\' : '\\', '\'' : '\'', '"' : '"', '`' : '`', '0' : '\0'];
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

Nullable!T parseStringLiteral(T)(ref string file, void delegate(string) error) {
	string err;
	auto str = readString(file, T.charCode, T.charCode, err);
	if (err) {
		error(err);
	}
	if (str) {
		return typeof(return)(T(str));
	}
	return typeof(return).init;
}

Nullable!Eof parseEOF(ref string file, void delegate(string) error) {
	if (file.length == 0) {
		return typeof(return)(Eof());
	}
	return typeof(return).init;
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

alias Parsers = AliasSeq!(parseEOF, parseIdentifier, parseIntLiteral, parseStringLiteral!CharLiteral, parseStringLiteral!StringLiteral, staticMap!(parseKeyword, keywords), staticMap!(parseOperator, operators));

auto slice(string file, size_t index) {
	return file[index .. $];
}

auto unslice(string file, string subset) {
	return subset.ptr - file.ptr;
}

struct Lexer {
	Source source;
	uint line;
	size_t index;
	size_t lineStart;

	this(string fileName, string file) {
		this.source = Source(fileName, file);
		this.line = 1;
		popFront;
	}

	Token front;

	@property bool empty() {
		return front == Eof();
	}

	@property auto save() {
		return this;
	}

	void popFront() {
		auto sliced = slice(source.file, index);
		sliced.removeComments;

		Position position() {
			auto untilLine = countUntil(sliced, "\n");
			if (untilLine == -1) {
				untilLine = sliced.length;
			}
			auto end = unslice(source.file, sliced);
			auto lineCount = cast(uint) source.file[index .. end].filter!(a => a == '\n').count;

			return Position(source, Section(line, line + lineCount, index, end, lineStart, end + untilLine));
		}

		void quit(string message) {
			error(message, position());
		}

		static foreach (parser; Parsers) {
			{
				auto token = parser(sliced, &quit);
				if (!token.isNull) {
					front.value = typeof(front.value)(token.get);
					front.position = position();
					auto end = unslice(source.file, sliced);
					size_t nextLine = source.file[index .. end].retro.countUntil("\n");
					if (nextLine != -1) {
						lineStart = end - nextLine;
					}
					line += cast(int) source.file[index .. end].filter!(a => a == '\n').count;
					index = end;
					return;
				}
			}
		}
		error("Unknown Token", position());
	}

	auto expect(T...)(T expected) if (T.length == 1) {
		if (front != expected) {
			error("Expected " ~ expected.to!string, front.position);
		}
	}

	auto expect(T...)(T expectedList) if (T.length != 1) {
		foreach (expected; expectedList) {
			if (front == expected) {
				return;
			}
		}
		error("Expected " ~ T.stringof, front.position);
	}

	auto expectType(T)() {
		if (auto wanted = front.value.peek!T) {
			return *wanted;
		}
		error("Expected " ~ T.stringof, front.position);
		assert(0);
	}
}
