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

import std.typecons;

Tuple!()[T] arrayToSet(T)(T[] data) {
	Tuple!()[T] result;
	foreach (d; data) {
		result[d] = tuple();
	}
	return result;
}

T[] emptyArray(T)() {
	return null;
}

Tuple!()[T] emptySet(T)() {
	return null;
}

V[K] emptyMap(K, V)() {
	return null;
}

Tuple!()[T] singleSet(T)(T data) {
	return arrayToSet([data]);
}

Tuple!()[T] mergeSets(T)(Tuple!()[T] left, Tuple!()[T] right) {
	return arrayToSet(left.keys ~ right.keys);
}

auto mergeSets(H, T...)(H first, H second, T tail) if (tail.length > 0) {
	return mergeSets(mergeSets(first, second), tail);
}

auto intersectSets(T)(Tuple!()[T] left, Tuple!()[T] right) {
	Tuple!()[T] result;
	foreach (e; left.byKey) {
		if (e in right) {
			result[e] = tuple();
		}
	}
	return result;
}

bool isSubSet(T)(Tuple!()[T] smaller, Tuple!()[T] bigger) {
	foreach (key; smaller.byKey) {
		if (!(key in bigger)) {
			return false;
		}
	}
	return true;
}

Tuple!(V, V)[K] intersectMaps(K, V)(V[K] left, V[K] right) {
	Tuple!(V, V)[K] result;
	foreach (leftKey, leftValue; left) {
		if (leftKey in right) {
			result[leftKey] = tuple(leftValue, right[leftKey]);
		}
	}
	return result;
}

V[K] mergeMaps(alias combine, K, V)(V[K] left, V[K] right) {
	V[K] result;
	foreach (k; left.byKey) {
		result[k] = left[k];
	}
	foreach (k; right.byKey) {
		if (k in result) {
			result[k] = combine(result[k], right[k]);
		} else {
			result[k] = right[k];
		}
	}
	return result;
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

auto mapValues(alias fun, K, V)(V[K] data) {
	typeof(fun(V.init))[K] fresh;
	foreach (key, value; data) {
		fresh[key] = fun(value);
	}
	return fresh;
}
