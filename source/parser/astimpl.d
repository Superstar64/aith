module parser.astimpl;

import parser.ast;
import misc;

import std.algorithm;
import std.array;

class Impl(T : Expression) : T {
	this() {
	}

	mixin Getters!T;
	override Pattern patternMatch() {
		return patternMatchImpl(this);
	}
}

class Impl(T) : T {
	this() {
	}

	mixin Getters!T;
}

Pattern patternMatchImpl(T)(T that) {
	return null;
}

Pattern patternMatchImpl(Variable that) {
	auto result = make!NamedArgument;
	result.position = that.position;
	result.name = that.name;
	return result;
}

Pattern patternMatchImpl(TupleLit that) {
	auto children = that.values.map!(a => a.patternMatch).array;
	if (children.any!(a => a is null)) {
		return null;
	} else {
		auto result = make!TupleArgument;
		result.position = that.position;
		result.matches = children;
		return result;
	}
}

auto make(T, A...)(A arguments) {
	return new Impl!T(arguments);
}
