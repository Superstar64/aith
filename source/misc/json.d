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

module misc.json;

import std.algorithm;
import std.array;
import std.typecons;
import std.bigint;

import jsast;
import misc.nonstrict;

abstract class Json {
	void toExprString(scope void delegate(const(char)[]) result, uint indent, Tuple!() context);
	uint pred();

	override string toString() {
		string result;
		toExprString((const(char)[] str) { result ~= str; }, 0, tuple());
		return result;
	}
}

alias JsonInt = JsIntLitImpl!(Json, Tuple!());
alias JsonDouble = JsDoubleLitImpl!(Json, Tuple!());
alias JsonBool = JsBoolLitImpl!(Json, Tuple!());
alias JsonChar = JsCharLitImpl!(Json, Tuple!());
alias JsonArray = JsArrayImpl!(Json, Tuple!());
alias JsonObject = JsObjectImpl!(Json, Tuple!());

interface Jsonable {
	Json jsonify();
}

Json jsonify(int x) {
	return new JsonInt(x);
}

Json jsonify(BigInt x) {
	return new JsonInt(x);
}

Json jsonify(bool x) {
	return new JsonBool(x);
}

Json jsonify(string x) {
	return new JsonChar(x);
}

Json jsonify(T)(T[] list) {
	return new JsonArray(list.map!jsonify.array);
}

Json jsonify(V)(V[string] map) {
	JsonObject base = new JsonObject;
	foreach (name; map.byKey) {
		base.fields ~= tuple(name, map[name].jsonify);
	}
	return base;
}

Json jsonify(T)(Lazy!T x) {
	return x.get.jsonify;
}

Json jsonify(Jsonable that) {
	return that.jsonify();
}
