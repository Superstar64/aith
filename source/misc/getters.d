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

module misc.getters;

import std.traits;
import std.meta;

template GetMember(T) {
	alias GetMember(string name) = AliasSeq!(__traits(getMember, T, name));
}

alias PropertyNameTuple(T) = __traits(derivedMembers, T);

alias PropertyTypeTuple(T) = staticMap!(ReturnType, staticMap!(GetMember!T, PropertyNameTuple!T));

mixin template Getters(T) {
	import std.format;
	import std.traits;

	static foreach (field; PropertyNameTuple!T) {
		mixin(q{ private ReturnType!(__traits(getMember,T,field)) _%s;}.format(field));
		mixin(q{ override %s ReturnType!(__traits(getMember,T,field)) %s(){
				return _%s;
			}}.format(functionAttributes!(__traits(getMember, T, field)) & FunctionAttribute.ref_ ? "ref" : "", field, field));
	}
	this(PropertyTypeTuple!T arguments) {
		static foreach (c, field; PropertyNameTuple!T) {
			mixin(q{this._%s = arguments[c];}.format(field));
		}
	}

	auto properties()() {
		mixin(q{return .tuple(} ~ [PropertyNameTuple!T].map!(a => "_" ~ a ~ ",").joiner.array ~ q{);});
	}

	import misc.json;

	Json jsonifyImpl()() {
		static import std.typecons;
		static import std.conv;
		static import misc.json;

		JsonObject base = new JsonObject;
		base.fields ~= std.typecons.tuple("_name", misc.json.jsonify(T.stringof));
		//base.fields ~= std.typecons.tuple("_address", misc.jsonify(std.conv.to!string(cast(void*)(this))) );
		static foreach (c, field; PropertyNameTuple!T) {
			mixin(q{base.fields ~= std.typecons.tuple("%s",this.%s.jsonify);}.format(field, field));
		}
		return base;
	}
}
