import std.conv : to;

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

T castTo(T, Base)(Base node) {
	return cast(T) node;
}
