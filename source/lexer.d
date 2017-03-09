/+
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
import std.ascii : isAlpha, isAlphaNum, isDigit, isWhite;
import std.bigint : BigInt;
import std.conv : to;
import std.typecons : Nullable;
import std.variant : Algebraic;
import std.range : chunks;
import std.array : array;
import error : error;

@property {
	char front(string str) {
		return str[0];
	}

	void popFront(ref string str) {
		str = str[1 .. $];
	}

	bool empty(string str) {
		return str.length == 0;
	}
}
BigInt ctorBigInt(string s) {
	return BigInt(s);
}

struct Position { //used for token position in a file
	string file_name;
	uint line;
	string file; //ref to file
	size_t indexs; //file index start
	size_t indexe; //file index end
	auto join(Position other) {
		assert(file_name == other.file_name, file_name ~ " " ~ other.file_name);
		assert(file.ptr == other.file.ptr);
		return Position(file_name, line, file, indexs, other.indexs);
	}

	string toString() {
		return file[indexs .. indexe];
	}
}

struct Identifier {
	string name;
	alias name this;
	static Nullable!Identifier consume(ref string file) {
		if (file.front.isAlpha || file.front == '_') {
			auto org = file;
			do {
				file.popFront;
			}
			while (!file.empty && (file.front.isAlphaNum || file.front == '_'));
			return typeof(return)(Identifier(org[0 .. org.length - file.length]));
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
			auto org = file;
			do {
				file.popFront;
			}
			while (!file.empty && file.front.isDigit);
			auto number = org[0 .. org.length - file.length];
			return typeof(return)(IntLiteral(ctorBigInt(number)));
		}
		return typeof(return).init;
	}
}

struct Keyword {
	enum list = [
			"alias", "auto", "bool_t", //"catch",
			"char", "else", //"end",
			"enum", "extern", "false",
			//"float_t",
			//"function",
			"if", "import", "int_t", //"is",
			//"label",
			"new", "of", "return", //"spawn"//thread;
			"then", //"throw",
			//"throws",
			"true", //"typedef",
			//"type_template",
			"uint_t", //"union",
			//"value_template",
			"while", //"yield"//coroutine, acts like return but on next call will continue from yield point
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
	enum list = [ //todo template syntax
			"<<=", //must be sorted according to string length
			">>=", ">>>", "==", "!=", "<=", ">=", "<<", ">>", "&&",
			"||", "+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=", "~=", "::",
			"~>", "~<", "..", "<", ">", "+", "-", "*", "/", "%", "=", "!",
			"~", "&", "|", "^", ":", "$", "@", //"#",
			"{", "}", "(", ")", "[", "]", ".", ",", ";"
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

string readStringLit(ref string file, char start, char end, out string err) {
	if (file.front != start) {
		return null;
	}
	file.popFront;
	if (file.empty) {
		err = "Expected " ~ end;
		return null;
	}
	string old = file;
	reader: while (true) {
		if (file.front == '\\') {
			old = old[0 .. old.length - file.length];
			while (true) {
				if (file.front == '\\') {
					file.popFront;
					if (file.empty) {
						err = "Expected escape character after \\";
						return null;
					}
					if (file.front == 'a') {
						old ~= '\a';
					} else if (file.front == 'b') {
						old ~= '\b';
					} else if (file.front == 'f') {
						old ~= '\f';
					} else if (file.front == 'n') {
						old ~= '\n';
					} else if (file.front == 'r') {
						old ~= '\r';
					} else if (file.front == 't') {
						old ~= '\t';
					} else if (file.front == 'v') {
						old ~= '\v';
					} else if (file.front == '\\') {
						old ~= '\\';
					} else if (file.front == '\'') {
						old ~= '\'';
					} else if (file.front == '"') {
						old ~= '"';
					} else if (file.front == '`') {
						old ~= '`';
					} else if (file.front == '0') {
						old ~= '\0';
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
						foreach (c; text.chunks(2)) { //untested
							old ~= c.array.to!ubyte(16);
						}
					} else {
						err = "Expected escape character after \\";
						return null;
					}
					file.popFront;
					if (file.empty) {
						err = "Expected escape character after \\";
						return null;
					}
					continue;
				}
				if (file.front == end) {
					break reader;
				}
				old ~= file.front;
				file.popFront;
				if (file.empty) {
					err = "Expected " ~ end;
					return null;
				}
			}
		}
		if (file.front == end) {
			old = old[0 .. old.length - file.length];
			break;
		}
		file.popFront;
		if (file.empty) {
			err = "Expected " ~ end;
			return null;
		}
	}
	file.popFront;
	return old;
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
	Algebraic!(Identifier, IntLiteral, Keyword, Operator, CharLiteral, StringLiteral,
		Eof) value;
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
					return 0;
				}
			}
		}
		error("Expected " ~ T.stringof, pos);
		return typeof(return).init;
	}

	@property void expect(T)(T t) {
		if (value != t) {
			error("Expected " ~ t.to!string, pos);
		}
	}
}

void cleanComment(ref string file) {
	if (file.empty) {
		return;
	}
	if (file.front.isWhite) {
		file.popFront;
		return file.cleanComment;
	}
	if (file.front == '#') {
		file.popFront;
		if (file.empty)
			return;
		if (file.front == '$') { //multiline comment
			uint count = 1;
			do {
				file.popFront;
				if (file.empty)
					return;
				if (file.front == '#') {
					auto cpy = file;
					cpy.popFront;
					if (cpy.empty)
						return;
					if (cpy.front == '$') {
						cpy.popFront;
						file = cpy;
						count++;
					}
				} else if (file.front == '$') {
					auto cpy = file;
					cpy.popFront;
					if (cpy.empty)
						return;
					if (cpy.front == '#') {
						cpy.popFront;
						if (cpy.empty)
							return;
						file = cpy;
						count--;
						if (count == 0) {
							return file.cleanComment;
						}
					}
				}
			}
			while (true);
		} else {
			while (!file.empty && file.front != '\n') {
				file.popFront;
			}
			if (file.empty)
				return;
			file.popFront;
			if (file.empty)
				return;
			return file.cleanComment;
		}
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
			auto old = file;
			file.cleanComment();
			diff(old);
		}
		auto pos = Position(file_name, cline, file_org, cindex);
		scope (success) {
			pos.indexe = cindex;
			front.pos = pos;
		}

		auto old = file;
		scope (success) {
			diff(old);
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

	void diff(string old) {
		foreach (c; old[0 .. old.length - file.length]) {
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

unittest {
	import std.file;

	auto lexer = Lexer("test/lexer", cast(string) read("test/lexer"));
	assert(lexer.front == IntLiteral(BigInt("1234")));
	lexer.popFront;
	assert(lexer.front == oper!"(");
	lexer.popFront;
	assert(lexer.front == oper!"+");
	lexer.popFront;
	assert(lexer.front == Identifier("hi"));
	lexer.popFront;
	assert(lexer.front == CharLiteral("char literal"));
	lexer.popFront;
	assert(lexer.front == StringLiteral("string\tliteral"));
	lexer.popFront;
	assert(lexer.front == Eof());
	assert(lexer.empty);
}
