//comparing

const typi_compare_vanilla = ([left, right]) => left === right;

const typi_array_compare = compare => ([left, right]) => {
	if (left.length != right.length) {
		return false;
	}
	for (let i = 0; i < left.length; i++) {
		if (!compare([left.data[left.start + i], right.data[right.start + i]])) {
			return false;
		}
	}
	return true;
};

const typi_tuple_compare = subcompares => ([left,right]) => {
	for (let i = 0; i < subcompares.length; i++) {
		if (!subcompares[i]([left[i], right[i]])) {
			return false;
		}
	}
	return true;
};

const typi_compare_not = compare => ([left,right]) => !compare([left,right]);

//arrays

const typi_new_array = ([length, element]) => {
	const fresh = [];
	for (let i = 0; i < length; i++) {
		fresh[i] = element;
	}
	return {
		data: fresh,
		start: 0,
		length: length
	};
};

const typi_borrow_array = array => [array,array];

const typi_delete_array = array => [];

const typi_index_array = ([array, index]) => array.data[array.start + index];

const typi_array_slice = ([array, start, end]) => null || {
	data: array.data,
	start: array.start + start,
	length: end - start
};

const typi_array_length = array => array.length;

const typi_array_literal = length => elements => {
	const fresh = [];
	for (let i = 0; i < length; i++) {
		fresh[i] = elements[i];
	}
	return {
		data: fresh,
		start: 0,
		length: length
	};
};

//pointers

const typi_util_create_child_pointer = (tuple_pointer, index) => null || {
	get: () => tuple_pointer.get()[index],
	set: object => { 
		let clone = tuple_pointer.get().slice();
		clone[index] = object;
		tuple_pointer.set(clone);
	}
};


const typi_create_pointer = ([object, world]) => [{
	get: () => object,
	set: value => { object = value; }
}, undefined];

const typi_borrow_pointer = pointer => [pointer, pointer];

const typi_delete_pointer = ([pointer, world]) => [pointer.get(), undefined];

const typi_tuple_address_forword = (index,tuple_size) => tuple_pointer => {
	if(tuple_pointer.children === undefined){
		tuple_pointer.children = [];
		for(let i = 0; i < tuple_size; i++){
			tuple_pointer.children[i] = typi_util_create_child_pointer(tuple_pointer,i);
		}
	}
	return tuple_pointer.children[index]; 
};

const typi_array_address_of = ([array, index, world]) => {
	array.data.pointers = array.data.pointers || [];

	const pointers = array.data.pointers;
	const realIndex = array.start + index;
	pointers[realIndex] = pointers[realIndex] || {
		get: () => array.data[realIndex],
		set: object => { array.data[realIndex] = object; }
	};
	return [pointers[realIndex], undefined];
};


const typi_pointer_assign = ([pointer, value]) => {
	pointer.set(value);
	return [];
};

const typi_derefence_pointer = pointer => {
	return pointer.get();
};

// logic

const typi_and = ([left,right]) => {
	return left && right;
};

const typi_or = ([left,right]) => {
	return left || right;
}

const typi_not = boolean => !boolean;


// numbers

const typi_lessthan = (size, signed) => ([left,right]) => {
	return left < right;
};

const typi_lessthan_equal = (size, signed) => ([left,right]) => {
	return left <= right;
};

const typi_greater = (size, signed) => ([left,right]) => {
	return left > right;
};

const typi_greater_equal = (size, signed) => ([left,right]) => {
	return left >= right;
};

const typi_add = (size, signed) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left + right | 0;
	} else if(!signed && size == 32){
		return left + right >>> 0;
	} else {
		throw "Bad number size";
	}
};

const typi_subtract = (size, signed) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left - right | 0;
	} else if(!signed && size == 32){
		return left - right >>> 0;
	} else {
		throw "Bad number size";
	}
};
const typi_multiply = (size, signed) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left * right | 0;
	} else if(!signed && size == 32){
		return left * right >>> 0;
	} else {
		throw "Bad number size";
	}
};

const typi_divide = (size, signed) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left / right | 0;
	} else if(!signed && size == 32){
		return left / right >>> 0;
	} else {
		throw "Bad number size";
	}
};

const typi_modulus = (size, signed) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left % right | 0;
	} else if(!signed && size == 32){
		return left % right >>> 0;
	} else {
		throw "Bad number size";
	}
};

const typi_negate = (size, signed) => number => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return -number | 0;
	} else if(!signed && size == 32){
		return -number >>> 0;
	} else {
		throw "Bad number size";
	}
}

const typi_cast_integer = (size, signed) => (input_size, input_signed) => number => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return number | 0;
	} else if(!signed && size == 32){
		return number >>> 0;
	} else {
		throw "Bad number size";
	}
};

// tuples

const typi_index_tuple = index => tuple => {
	return tuple[index];
}; 

// misc

const write = ([argument, world]) => {
	console.log(argument.data);
	return undefined;
}

const assert = ([check, world]) => {
	if (!check) {
		console.trace("Error");
		throw "Assetion Error";
	}
	return undefined;
}

// generated code:
