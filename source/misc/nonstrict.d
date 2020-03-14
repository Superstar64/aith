module misc.nonstrict;

class Lazy(T) {
	T delegate() callback;
	struct Value {
		T val;
	}

	Value* value;

	this(T delegate() callback) {
		this.callback = callback;
	}

	T get() {
		if (value is null) {
			auto v = callback();
			value = new Value(v);
		}
		return value.val;
	}

	void eval() {
		get();
	}
}

Lazy!T defer(T)(T delegate() callback) {
	return new Lazy!T(callback);
}
