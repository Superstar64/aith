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

import misc.nonstrict;
import misc.json;

template Pack(T...) {
	alias expand = T;
}

template dispatch(alias fun, Types...) {
	auto dispatch(Base, T...)(Base base, auto ref T args) {
		foreach (Type; Types) {
			if (cast(Type) base) {
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
