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

module misc.container;

import std.algorithm : map, filter, all;
import std.array;
import std.range;
import std.typecons;

import std.conv;

struct Item(K, V) {
	K key;
	V value;
}

Item!(K, V) item(K, V)(K key, V value) {
	return Item!(K, V)(key, value);
}

struct OwnerDictonary(K, V) {
	@disable this(this);
	V[K] internal;

	ref V opIndex(K key) {
		return internal[key];
	}

	void remove(K key) {
		assert(key in internal);
		internal.remove(key);
	}

	void insert(K key, lazy V value) {
		assert(!(key in internal));
		internal[key] = value;
	}

	bool opBinaryRight(string op : "in")(K key) {
		return !!(key in internal);
	}

	int opApply(int delegate(K, ref V) f) {
		int x;
		foreach (k, ref v; internal) {
			x = f(k, v);
			if (x) {
				return x;
			}
		}
		return x;
	}

	auto range() {
		return internal.byKeyValue;
	}

	auto byKey() {
		return internal.byKey;
	}

	auto byValue() {
		return internal.byValue;
	}

	void clear() {
		internal.clear();
	}

	Dictonary!(K, V) freeze() {
		auto result = Dictonary!(K, V)(internal);
		internal = null;
		return result;
	}
}

struct Dictonary(K, V) {
	V[K] internal;

	// don't modify
	// can't be const because transitive const ruins V
	ref V opIndex(K key) {
		return internal[key];
	}

	bool opBinaryRight(string op : "in")(K key) {
		return !!(key in internal);
	}

	size_t length() {
		return internal.length;
	}

	auto range() {
		return internal.byKeyValue;
	}

	auto byKey() {
		return internal.byKey;
	}

	auto byValue() {
		return internal.byValue;
	}

	int opApply(int delegate(K, ref V) f) {
		int x;
		foreach (k, ref v; internal) {
			x = f(k, v);
			if (x) {
				return x;
			}
		}
		return x;
	}

	static if (is(V : Tuple!())) {
		int opApply(int delegate(K) f) {
			int x;
			foreach (k, ref v; internal) {
				x = f(k);
				if (x) {
					return x;
				}
			}
			return x;
		}

		string toString() {
			return byKey.to!string;
		}
	} else {
		string toString() {
			return internal.to!string;
		}
	}
}

Dictonary!(K, V) replaceCopy(K, V)(Dictonary!(K, V) that, K key, V value) {
	return that.removeCopy(key).insertCopy(key, value);
}

Set!K insertCopy(K)(Dictonary!(K, Tuple!()) that, K key, Tuple!() value = Tuple!()()) {
	alias V = Tuple!();
	assert(!(key in that.internal));
	V[K] result;
	foreach (k, v; that.internal) {
		result[k] = v;
	}
	result[key] = value;
	return Dictonary!(K, V)(result);
}

Dictonary!(K, V) insertCopy(K, V)(Dictonary!(K, V) that, K key, V value) if (!is(V : Tuple!())) {
	assert(!(key in that.internal));
	V[K] result;
	foreach (k, v; that.internal) {
		result[k] = v;
	}
	result[key] = value;
	return Dictonary!(K, V)(result);
}

Dictonary!(K, V) removeCopy(K, V)(Dictonary!(K, V) that, K key) {
	assert(key in that.internal);
	V[K] result;
	foreach (k, v; that.internal) {
		result[k] = v;
	}
	result.remove(key);
	return Dictonary!(K, V)(result);
}

Dictonary!(K, V) singletonMap(K, V)(K key, V value) {
	return emptyMap!(K, V).insertCopy(key, value);
}

Dictonary!(K, V) insertRangeMap(R, K, V)(Dictonary!(K, V) that, R range) {
	auto copy = that.internal.dup;
	foreach (item; range) {
		assert(!(item.key in that.internal));
		copy[item.key] = item.value;
	}
	return Dictonary!(K, V)(copy);
}

Dictonary!(K, V) removeRange(R, K, V)(Dictonary!(K, V) that, R range) {
	auto copy = that.internal.dup;
	foreach (key; range) {
		assert(key in that.internal);
		copy.remove(key);
	}
	return Dictonary!(K, V)(copy);
}

Dictonary!(K, V) removeRangeIfExists(R, K, V)(Dictonary!(K, V) that, R range) {
	return that.removeRange(range.filter!(a => a in that));
}

Dictonary!(K, V) rangeToMap(R, K = typeof(R.init.front.key), V = typeof(R.init.front.value))(R range) {
	return emptyMap!(K, V).insertRangeMap(range);
}

Dictonary!(K, V) insertIfMissing(K, V)(Dictonary!(K, V) that, K key, V value) {
	if (!(key in that)) {
		return that.insertCopy(key, value);
	} else {
		return that;
	}
}

Dictonary!(K, V) removeIfExists(K, V)(Dictonary!(K, V) that, K key) {
	if (key in that) {
		return that.removeCopy(key);
	} else {
		return that;
	}
}

Set!K keys(K, V)(Dictonary!(K, V) that) {
	return that.byKey.rangeToSet;
}

alias Set(T) = Dictonary!(T, Tuple!());

Set!T insertRangeSet(R, T)(Dictonary!(T, Tuple!()) that, R range) {
	return that.insertRangeMap(range.map!(a => item(a, tuple())));
}

Set!T rangeToSet(R, T = ElementType!R)(R range) {
	return emptySet!T().insertRangeSet(range);
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

Set!T intersectSets(T)(Dictonary!(T, Tuple!()) left, Dictonary!(T, Tuple!()) right) {
	return left.byKey.filter!(a => a in right).rangeToSet;
}

bool isSubSet(T)(Dictonary!(T, Tuple!()) smaller, Dictonary!(T, Tuple!()) bigger) {
	return smaller.byKey.map!(a => a in bigger).all;
}

Set!T mergeSets(T)(Dictonary!(T, Tuple!()) left, Dictonary!(T, Tuple!()) right) {
	return mergeMapsLeft(left, right);
}

Dictonary!(K, Tuple!(V, V)) intersectMaps(K, V)(Dictonary!(K, V) left, Dictonary!(K, V) right) {
	auto keys = left.byKey.filter!(a => a in right);
	return keys.map!(key => item(key, tuple(left[key], right[key]))).rangeToMap;
}

Dictonary!(K, V) mergeMaps(alias combine, K, V)() {
	return Dictonary!(K, V)();
}

Dictonary!(K, V) mergeMaps(alias combine, K, V)(Dictonary!(K, V) that) {
	return that;
}

Dictonary!(K, V) mergeMaps(alias combine, K, V)(Dictonary!(K, V) left, Dictonary!(K, V) right) {
	return chain(left.range.filter!(a => !(a.key in right)), right.range.filter!(a => !(a.key in left)), intersectMaps(left, right).mapValues!(x => combine(x[0], x[1])).range).rangeToMap;
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

auto mapValues(alias fun, K, V)(Dictonary!(K, V) data) {
	Dictonary!(K, typeof(fun(V.init))) result;
	foreach (key, value; data) {
		result = result.insertCopy(key, fun(value));
	}
	return result;
}
