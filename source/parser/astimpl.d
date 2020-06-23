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
module parser.astimpl;

import std.algorithm;
import std.array;

import parser.ast;

import misc.getters;
import misc.position;

class Impl(T : Expression) : Getters!T {
	this(A...)(A arguments) {
		super(arguments);
	}

	override Pattern patternMatch() {
		return patternMatchImpl(this);
	}

	import Semantic = semantic.ast;
	import semantic.semantic : Context, semanticImpl;

	override Semantic.Expression semanticMain(Context context) {
		return semanticImpl(this, context);
	}
}

class Impl(T : Pattern) : Getters!T {
	this(A...)(A arguments) {
		super(arguments);
	}

	import Semantic = semantic.ast;
	import semantic.semantic : Context, semanticImpl;

	override Semantic.Expression semanticMain(Context context) {
		return semanticImpl(this, context);
	}
}

class Impl(T) : Getters!T {
	this(A...)(A arguments) {
		super(arguments);
	}
}

Pattern patternMatchImpl(T)(T that) {
	error("Expected pattern", that.position);
	assert(0);
}

Pattern patternMatchImpl(Variable that) {
	return make!NamedArgument(that.position, that.name, that.shadow);
}

Pattern patternMatchImpl(TupleLit that) {
	return make!TupleArgument(that.position, that.values.map!(a => a.patternMatch).array);
}

auto make(T, A...)(A arguments) {
	return new Impl!T(arguments);
}
