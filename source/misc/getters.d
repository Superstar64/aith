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

module misc.getters;

import std.traits : ReturnType;
import std.meta : staticMap;

template GetMember(T) {
	alias GetMember(string name) = __traits(getMember, T, name);
}

alias PropertyTypeTuple(T) = staticMap!(ReturnType, staticMap!(GetMember!T, __traits(derivedMembers, T)));

abstract class Getters(T) : T {
	import std.format : format;
	import std.algorithm : canFind;
	import std.traits : ReturnType, Parameters, MemberFunctionsTuple;

	enum _properties = cast(string[])[__traits(derivedMembers, T)];

	static foreach (member; __traits(allMembers, T)) {
		static if (!_properties.canFind(member)) {
			static foreach (instance; MemberFunctionsTuple!(T, member)) {
				mixin(q{
					override abstract ReturnType!instance %s (Parameters!instance arguments);
				}.format(member));
			}
		}
	}

	static foreach (field; _properties) {
		mixin(q{
			private ReturnType!(__traits(getMember,T,field)) _%s;
			override ReturnType!(__traits(getMember,T,field)) %s(){
				return _%s;
			}
		}.format(field, field, field));
	}

	this(PropertyTypeTuple!T arguments) {
		static foreach (c, field; _properties) {
			mixin(q{this._%s = arguments[c];}.format(field));
		}
	}

	auto _fields()() {
		import std.typecons : tuple;
		import std.conv : to;
		import std.algorithm : map, joiner;

		mixin(q{ return tuple (} ~ _properties.map!(a => a ~ ",")
				.joiner
				.to!string ~ q{);});
	}

}

auto destructure(alias c, T)(Getters!T object) {
	return c(object._fields.expand);
}
