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
import std.conv;
import misc.json;

class SymbolId : Jsonable {
	override Json jsonify() {
		return new JsonChar((cast(void*) this).to!string);
	}
}

class VarId : Jsonable {
	override Json jsonify() {
		return new JsonChar((cast(void*) this).to!string);
	}
}
