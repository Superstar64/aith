import std.conv;
import jsast;

class SymbolId {
}

class VarId {
}

Json jsonify(SymbolId symbol) {
	return new JsonChar((cast(void*) symbol).to!string);
}

Json jsonify(VarId var) {
	return new JsonChar((cast(void*) var).to!string);
}
