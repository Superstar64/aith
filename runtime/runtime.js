// utililty
var tagged = function(id, value) {
	return {
		id: id,
		value: value
	};
};

var match = function(union, matches) {
	return matches[union.id](union.value);
};

//runtime typi info

var typi_type_int = function(signed, size) {
	return tagged(0, [signed, size]);
};

var typi_type_char = tagged(1, []);

var typi_type_bool = tagged(2, []);

var typi_type_tuple = function(types) {
	return tagged(3, types);
};

var typi_type_array = function(value) {
	return tagged(4, value);
};

var typi_type_pointer = function(value) {
	return tagged(5, value);
};

var typi_type_function = function(argument, result) {
	return tagged(6, [argument, result]);
};

// type utility

var typi_constant = function(value) {
	return function(ignore) {
		return value;
	};
};

var typi_assign_vanilla = function(current, index, value) {
	current[index] = value;
}

var typi_assign_vanilla_constant = typi_constant(typi_assign_vanilla);

var typi_tuple_assign = function(subtypes) {
	var subassign = [];
	for (var i = 0; i < subtypes.length; i++) {
		subassign[i] = typi_assign(subtypes[i]);
	}
	return function(current, index, value) {
		for (var i = 0; i < subassign.length; i++) {
			current[index] = current[index] || [];
			subassign[i](current[index], i, value[i]);
		}
	};
};

var typi_assign = function(type) {
	var vanilla = typi_assign_vanilla_constant;
	return match(type, [
		vanilla,
		vanilla,
		vanilla,
		typi_tuple_assign,
		vanilla,
		vanilla,
		vanilla
	]);
};

var typi_pointer_to = function(type) {
	var assign = typi_assign(type);
	return function(object, index) {
		var children = [];
		return {
			get: function() {
				return object[index];
			},
			set: function(value) {
				return assign(object, index, value);
			},
			child: type.id == 3 ? function(subindex) {
				var subtype = type.value[subindex];
				children[subindex] = children[subindex] || typi_pointer_to(subtype)(object[index], subindex);
				return children[subindex];
			} : undefined
		};
	};
};

//comparing

var typi_compare_vanilla = function(left, right) {
	return left == right;
};

var typi_compare_vanilla_constant = typi_constant(typi_compare_vanilla);

var typi_tuple_compare = function(subtypes) {
	var subcompares = [];
	for (var i = 0; i < subtypes.length; i++) {
		subcompares[i] = typi_compare(subtypes[i]);
	}
	return function(left, right) {
		for (var i = 0; i < subcompares.length; i++) {
			var subtype = subtypes[i];
			if (!subcompares[i](left[i], right[i])) {
				return false;
			}
		}
		return true;
	};
};

var typi_array_compare = function(subtype) {
	var compare = typi_compare(subtype);
	return function(left, right) {
		if (left.length != right.length) {
			return false;
		}
		for (var i = 0; i < left.length; i++) {
			if (!compare(left.data[left.start + i], right.data[right.start + i])) {
				return false;
			}
		}
		return true;
	};
};

var typi_compare = function(type) {
	var vanilla = typi_compare_vanilla_constant;
	return match(type, [
		vanilla,
		vanilla,
		vanilla,
		typi_tuple_compare,
		typi_array_compare,
		vanilla,
		function(x) {
			throw "comparing functions"
		}
	]);
};


//arrays

var typi_new_array = function(type) {
	var assign = typi_assign(type);
	return function(length, element) {
		var fresh = [];
		for (var i = 0; i < length; i++) {
			assign(fresh, i, element);
		}
		return {
			data: fresh,
			start: 0,
			length: length
		};
	};
};

var typi_index_array = function(array, index) {
	return array.data[array.start + index];
};

var typi_array_slice = function(array, start, end) {
	return {
		data: array.data,
		start: array.start + start,
		length: end - start
	};
};

var typi_array_length = function(array) {
	return array.length;
};


var typi_array_literal = function(type, length) {
	var assign = typi_assign(type);
	return function(elements) {
		var fresh = [];
		for (var i = 0; i < length; i++) {
			assign(fresh, i, elements[i]);
		}
		return {
			data: fresh,
			start: 0,
			length: length
		};
	};
};

//pointers


var typi_create_pointer = function(type) {
	var assign = typi_assign(type);
	var create = typi_pointer_to(type);
	return function(value) {
		var fresh = [null];
		assign(fresh, 0, value);
		return create(fresh, 0);
	};
};

var typi_array_address_of = function(type) {
	var create = typi_pointer_to(type);
	return function(array, index) {
		array.data.pointers = array.data.pointers || [];

		var pointers = array.data.pointers;
		var realIndex = array.start + index;
		pointers[realIndex] = pointers[realIndex] || create(array.data, realIndex);
		return pointers[realIndex];
	};
};


var typi_tuple_address_forword = function(tuple_pointer, index) {
	return tuple_pointer.child(index);
};

var typi_pointer_assign = function(pointer, value) {
	return pointer.set(value);
};

var typi_derefence_pointer = function(pointer) {
	return pointer.get();
};

// misc

var write = function(argument) {
	console.log(argument.data);
}

var assert = function(check) {
	if (!check) {
		console.trace("Error");
		throw "Assetion Error";
	}
}
