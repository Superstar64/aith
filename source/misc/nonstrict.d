module misc.nonstrict;

class Lazy(T) {
	T delegate() callback;
	Value* value;
	struct Value {
		T inner;
	}

	this(T value) {
		this.value = new Value(value);
	}

	this(T delegate() callback) {
		this.callback = callback;
	}

	T get() {
		if (value is null) {
			value = new Value(callback());
		}
		callback = null;
		return value.inner;
	}

	void eval() {
		get();
	}
}

Lazy!T defer(T)(T delegate() callback) {
	return new Lazy!T(callback);
}

Lazy!T eager(T)(T value) {
	return new Lazy!T(value);
}
