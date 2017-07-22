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
import std.algorithm : startsWith;
import std.ascii : isAlpha, isAlphaNum, isDigit, isWhite;
import std.bigint : BigInt;
import std.conv : to;
import std.typecons : Nullable;
import std.variant : Algebraic;
import std.range : chunks;
import std.array : array;

import error : error, Position;

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
}

struct Identifier {
	string name;
	alias name this;
	static Nullable!Identifier consume(ref string file) {
		if (file.front.isAlpha || file.front == '_') {
			auto original = file;
			do {
				file.popFront;
			}
			while (!file.empty && (file.front.isAlphaNum || file.front == '_'));
			return typeof(return)(Identifier(original[0 .. original.length - file.length]));
		}
		return typeof(return).init;
	}
}

struct IntLiteral {
	BigInt num;
	alias num this;
	this(this) {

	}

	auto opAssign(typeof(this) other) {
		num = other.num;
	}

	static Nullable!IntLiteral consume(ref string file) {
		if (file.front.isDigit) {
			auto original = file;
			do {
				file.popFront;
			}
			while (!file.empty && file.front.isDigit);
			auto number = original[0 .. original.length - file.length];
			return typeof(return)(IntLiteral(BigInt(number)));
		}
		return typeof(return).init;
	}
}

struct Keyword {
	enum list = [
			"alias", "let", "bool_t", "cast", "char", "else", "extern", "false",
			"if", "import", "int_t", "new", "of", "then", "true", "uint_t", "while",
		];
	size_t index;
	string toString() {
		return list[index];
	}

	static Nullable!Keyword opBinary(string op)(string candidate) if (op == "in") { //converts given string to a key word
		foreach (c, k; list) {
			if (k == candidate) {
				return typeof(return)(Keyword(c));
			}
		}
		return typeof(return).init;
	}
}

template key(string s) {
	auto findKey() {
		foreach (c, k; Keyword.list) {
			if (k == s) {
				return Keyword(c);
			}
		}
		assert(0, "unable to find keyword " ~ s);
	}

	enum key = findKey();
}

struct Operator {
	enum list = [
			//must be sorted according to string length
			"(*)", "==", "!=", "<=", ">=", "&&", "||", "::", "$@", "->", "..",
			"<", ">", "+", "-", "*", "/", "%", "=", "!", "~", "&", "|", "^",
			":", "$", "@", "{", "}", "(", ")", "[", "]", ".", ",", ";"
		];
	size_t index;
	string toString() {
		return list[index];
	}

	static Nullable!Operator consume(ref string file) {
		foreach (c, k; list) {
			if (k.length > file.length) {
				continue;
			}
			if (k == file[0 .. k.length]) {
				file = file[k.length .. $];
				return typeof(return)(Operator(c));
			}
		}
		return typeof(return).init;
	}
}

template oper(string s) {
	auto findOper() {
		foreach (c, o; Operator.list) {
			if (o == s) {
				return Operator(c);
			}
		}
		assert(0, "unable to find operator " ~ s);
	}

	enum oper = findOper();
}

string readStringLitWithEscapes(ref string file, char end, string current, out string err) {
	while (true) {
		if (file.front == '\\') {
			file.popFront;
			if (file.empty) {
				err = "Expected escape character after \\";
				return null;
			}
			if (file.front == 'a') {
				current ~= '\a';
			} else if (file.front == 'b') {
				current ~= '\b';
			} else if (file.front == 'f') {
				current ~= '\f';
			} else if (file.front == 'n') {
				current ~= '\n';
			} else if (file.front == 'r') {
				current ~= '\r';
			} else if (file.front == 't') {
				current ~= '\t';
			} else if (file.front == 'v') {
				current ~= '\v';
			} else if (file.front == '\\') {
				current ~= '\\';
			} else if (file.front == '\'') {
				current ~= '\'';
			} else if (file.front == '"') {
				current ~= '"';
			} else if (file.front == '`') {
				current ~= '`';
			} else if (file.front == '0') {
				current ~= '\0';
			} else if (file.front == '-') {
				file.popFront;
				if (file.empty) {
					err = "Expected hexadecmial";
					return null;
				}
				string text = file;
				while (file.front != '-') {
					file.popFront;
					if (file.empty) {
						err = "Expected -";
						return null;
					}
				}
				text = text[0 .. text.length - file.length];
				file.popFront;
				if (file.empty || file.front != '/') {
					err = "Expected /";
					return null;
				}

				if (text.length % 2 != 0) {
					err = "Bad Length for hex literal";
					return null;
				}
				foreach (c; text.chunks(2)) {
					current ~= c.array.to!ubyte(16);
				}
			} else {
				err = "Expected escape character after \\";
				return null;
			}
			file.popFront;
		}
		if (file.front == end) {
			file.popFront;
			return current;
		}
		current ~= file.front;
		file.popFront;
		if (file.empty) {
			err = "Expected " ~ end;
			return null;
		}
	}
}

string readStringLit(ref string file, char start, char end, out string err) {
	if (file.front != start) {
		return null;
	}
	file.popFront;
	if (file.empty) {
		err = "Expected " ~ end;
		return null;
	}
	string original = file;
	while (true) {
		if (file.front == '\\') {
			return readStringLitWithEscapes(file, end,
					original[0 .. original.length - file.length], err);
		}
		if (file.front == end) {
			original = original[0 .. original.length - file.length];
			file.popFront;
			return original;
		}
		file.popFront;
		if (file.empty) {
			err = "Expected " ~ end;
			return null;
		}
	}
}

struct CharLiteral {
	string data;
	static Nullable!CharLiteral consume(ref string file, out string err) {
		auto str = readStringLit(file, '\'', '\'', err);
		if (str && !err) {
			return typeof(return)(CharLiteral(str));
		}
		return (typeof(return)).init;
	}
}

struct StringLiteral {
	string data;
	static Nullable!StringLiteral consume(ref string file, out string err) {
		auto str = readStringLit(file, '"', '"', err);
		if (str && !err) {
			return typeof(return)(StringLiteral(str));
		}
		return (typeof(return)).init;
	}
}

struct Eof {

}

struct Token {
	Position pos;
	Algebraic!(Identifier, IntLiteral, Keyword, Operator, CharLiteral, StringLiteral, Eof) value;
	alias value this;
	bool opEquals(Token other) {
		return value == other.value;
	}

	bool opEquals(T)(T t) if (!is(T == Token)) {
		return value == t;
	}

	auto opAssign(T)(T val) {
		value = val;
		return this;
	}

	auto opAssign(T : Token)(T token) {
		pos = token.pos;
		value = token.value;
	}

	@property auto ref expectT(T...)() {
		foreach (a; T) {
			if (value.peek!a) {
				static if (T.length == 1) {
					return value.get!T;
				} else {
					return;
				}
			}
		}
		error("Expected " ~ T.stringof, pos);
		assert(0);
	}

	@property void expect(T)(T t) {
		if (value != t) {
			error("Expected " ~ t.to!string, pos);
		}
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
	return file.removeSingleLine;
}

void removeComment(ref string file) {
	if (file.empty) {
		return;
	}
	if (file.front.isWhite) {
		file.popFront;
		file.removeComment;
	}
	if (file.startsWith("#/")) {
		file.popFrontN(2);
		file.removeMultiLine;
		file.removeComment;
	}
	if (file.startsWith("#")) {
		file.removeSingleLine;
		return file.removeComment;
	}
}

struct Lexer {
	string file_name;
	uint cline = 1;
	uint cindex;
	string file;

	string file_org; //original file
	Token front;

	this(string file_name, string file) {
		this.file_name = file_name;
		this.file = file;
		this.file_org = file;
		popFront;
	}

	void popFront() {
		{ //clean whitespace,comments,etc
			auto original = file;
			file.removeComment();
			diff(original);
		}
		auto pos = Position(file_name, cline, file_org, cindex);
		scope (success) {
			pos.indexe = cindex;
			front.pos = pos;
		}

		auto original = file;
		scope (success) {
			diff(original);
		}

		if (file.empty) {
			front = Eof();
			return;
		}
		auto iden = Identifier.consume(file);
		if (!iden.isNull) {
			auto key = Keyword in iden.get.name;
			if (!key.isNull) {
				front = key.get;
				return;
			} else {
				front = iden.get;
				return;
			}
		}
		auto ilit = IntLiteral.consume(file);
		if (!ilit.isNull) {
			front = ilit.get;
			return;
		}
		auto ope = Operator.consume(file);
		if (!ope.isNull) {
			front = ope.get;
			return;
		}
		string err;
		auto chlit = CharLiteral.consume(file, err);
		if (err) {
			error(err, Position(file_name, cline, file, cindex, cindex + 1));
		}
		if (!chlit.isNull) {
			front = chlit.get;
			return;
		}
		auto stlit = StringLiteral.consume(file, err);
		if (err) {
			error(err, Position(file_name, cline, file, cindex, cindex + 1));
		}
		if (!stlit.isNull) {
			front = stlit.get;
			return;
		}
		error("Unknown Token", Position(file_name, cline, file, cindex, cindex + 1));
	}

	void diff(string original) {
		foreach (c; original[0 .. original.length - file.length]) {
			if (c == '\n') {
				cline++;
			}
			cindex++;
		}
	}

@property:
	bool empty() {
		return front == Eof();
	}

	auto save() {
		return this;
	}
}
