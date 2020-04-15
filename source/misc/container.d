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

module misc.container;

import std.algorithm : map, filter, all;
import std.array;
import std.range;
import std.typecons;

import std.conv;

struct Dictonary(K, V) {
	V[K] internal;

	V opIndex(K key) {
		return internal[key];
	}

	void opIndexAssign(V value, K key) {
		auto copy = internal.dup;
		copy[key] = value;
		internal = copy;
	}

	bool opBinaryRight(string op : "in")(K key) {
		return !!(key in internal);
	}

	size_t length() {
		return internal.length;
	}

	auto range() {
		return internal.byPair;
	}

	auto byKey() {
		return internal.byKey;
	}

	auto byValue() {
		return internal.byValue;
	}

	string toString() {
		return internal.to!string;
	}
}

Dictonary!(K, V) insertIfMissing(K, V)(Dictonary!(K, V) that, K key, V value) {
	if (!(key in that)) {
		return that.insert(key, value);
	} else {
		return that;
	}
}

Dictonary!(K, V) insert(K, V)(Dictonary!(K, V) that, K key, V value) {
	return that.insertRange(tuple(key, value).only);
}

Dictonary!(K, V) insertRange(R, K, V)(Dictonary!(K, V) that, R range) {
	auto copy = that.internal;
	foreach (key, value; range) {
		copy[key] = value;
	}
	return Dictonary!(K, V)(copy);
}

Dictonary!(K, V) rangeToMap(R, K = typeof(R.init.front[0]), V = typeof(R.init.front[1]))(R range) {
	return emptyMap!(K, V).insertRange(range);
}

Dictonary!(K, V) remove(K, V)(Dictonary!(K, V) that, K key) {
	return that.removeRange(key.only);
}

Dictonary!(K, V) removeRange(R, K, V)(Dictonary!(K, V) that, R range) {
	auto copy = that.internal;
	foreach (key; range) {
		copy.remove(key);
	}
	return Dictonary!(K, V)(copy);
}

Dictonary!(K, V) fromAALiteral(K, V)(V[K] literal) {
	assert(literal !is null);
	return Dictonary!(K, V)(literal);
}

Set!K keys(K, V)(Dictonary!(K, V) that) {
	return that.byKey.rangeToSet;
}

struct Set(T) {
	Dictonary!(T, Tuple!()) internal;

	auto range() {
		return internal.byKey;
	}

	bool opBinaryRight(string op : "in")(T item) {
		return item in internal;
	}

	string toString() {
		return range.to!string;
	}
}

Set!T insert(T)(Set!T that, T value) {
	return that.insertRange(value.only);
}

Set!T insertRange(R, T)(Set!T that, R range) {
	return Set!T(that.internal.insertRange(range.map!(a => tuple(a, tuple()))));
}

Set!T rangeToSet(R, T = ElementType!R)(R range) {
	return emptySet!T().insertRange(range);
}

T[] emptyArray(T)() {
	return null;
}

Set!T emptySet(T)() {
	return Set!T();
}

Dictonary!(K, V) emptyMap(K, V)() {
	return Dictonary!(K, V)();
}

Set!T intersectSets(T)(Set!T left, Set!T right) {
	return left.range.filter!(a => a in right).rangeToSet;
}

bool isSubSet(T)(Set!T smaller, Set!T bigger) {
	return smaller.range.map!(a => a in bigger).all;
}

Dictonary!(K, Tuple!(V, V)) intersectMaps(K, V)(Dictonary!(K, V) left, Dictonary!(K, V) right) {
	auto keys = left.byKey.filter!(a => a in right);
	return keys.map!(key => tuple(key, tuple(left[key], right[key]))).rangeToMap;
}

Dictonary!(K, V) mergeMaps(alias combine, K, V)() {
	return Dictonary!(K, V)();
}

Dictonary!(K, V) mergeMaps(alias combine, K, V)(Dictonary!(K, V) that) {
	return that;
}

Dictonary!(K, V) mergeMaps(alias combine, K, V)(Dictonary!(K, V) left, Dictonary!(K, V) right) {
	return left.insertRange(right.range.map!(a => tuple(a[0], a[0] in left ? combine(left[a[0]], a[1]) : a[1])));
}

auto mergeMaps(alias combine, H, T...)(H first, H second, T tail) if (tail.length > 0) {
	return mergeMaps!combine(mergeMaps!combine(first, second), tail);
}

T uniqueCombine(T)(T left, T right) {
	assert(0);
}

auto mergeMapsUnique(T...)(T arguments) {
	return mergeMaps!uniqueCombine(arguments);
}

T leftCombine(T)(T left, T right) {
	return left;
}

auto mergeMapsLeft(T...)(T arguments) {
	return mergeMaps!leftCombine(arguments);
}

T[] appendCombine(T)(T[] left, T[] right) {
	return left ~ right;
}

auto mergeMapsCombine(T...)(T arguments) {
	return mergeMaps!appendCombine(arguments);
}

auto mapValues(alias fun, K, V)(Dictonary!(K, V) data) {
	Dictonary!(K, typeof(fun(V.init))) result;
	foreach (key, value; data.range) {
		result = result.insert(key, fun(value));
	}
	return result;
}
