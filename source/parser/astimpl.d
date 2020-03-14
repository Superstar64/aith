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
module parser.astimpl;

import std.algorithm;
import std.array;

import parser.ast;

import misc.getters;

class Impl(T : Expression) : T {
	mixin Getters!T;
	override Pattern patternMatch() {
		return patternMatchImpl(this);
	}
}

class Impl(T) : T {
	mixin Getters!T;
}

Pattern patternMatchImpl(T)(T that) {
	return null;
}

Pattern patternMatchImpl(Variable that) {
	return make!NamedArgument(that.position, that.name);
}

Pattern patternMatchImpl(TupleLit that) {
	auto children = that.values.map!(a => a.patternMatch).array;
	if (children.any!(a => a is null)) {
		return null;
	} else {
		return make!TupleArgument(that.position, children);
	}
}

auto make(T, A...)(A arguments) {
	return new Impl!T(arguments);
}
