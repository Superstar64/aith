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

module misc.misc;

import std.conv;
import std.traits;
import std.algorithm;
import std.typecons;
import std.array;
import core.runtime;
import core.stdc.stdlib;
import std.stdio;
import std.meta;
import std.format;
import std.range;
import std.bigint;

import misc.json;

template Pack(T...) {
	alias expand = T;
}

template dispatch(alias fun, Types...) {
	auto dispatch(Base, T...)(Base base, auto ref T args) {
		foreach (Type; Types) {
			if (base.castTo!Type) {
				return fun(cast(Type) base, args);
			}
		}
		assert(0, base.to!string);
	}
}

template convert(T) {
	T convert(Base)(Base node) {
		return node;
	}
}

template castTo(T) {
	T castTo(Base)(Base node) {
		static assert(!is(Base : T), "use convert for safe casts");
		return cast(T)(node);
	}
}

T* wrap(T)(T term) {
	struct Wrapper {
		T inner;
	}

	auto object = new Wrapper;
	object.inner = term;
	return &object.inner;
}
