//comparing

const aith_compare_vanilla = ([left, right]) => left === right;

const aith_array_compare = compare => ([left, right]) => {
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

const aith_tuple_compare = subcompares => ([left,right]) => {
	for (let i = 0; i < subcompares.length; i++) {
		if (!subcompares[i]([left[i], right[i]])) {
			return false;
		}
	}
	return true;
};

const aith_compare = compare => ([left, right]) => compare([left, right]);
const aith_compare_not = compare => ([left,right]) => !compare([left,right]);

//arrays

const aith_new_array = _ => ([length, element, _]) => {
	const fresh = [];
	for (let i = 0; i < length; i++) {
		fresh[i] = element;
	}
	return [{
		data: fresh,
		start: 0,
		length: length
	}, undefined];
};

const aith_index_array = ([array, index, _]) => [array.data[array.start + index], undefined];

const aith_array_slice = ([array, start, end]) => null || {
	data: array.data,
	start: array.start + start,
	length: end - start
};

const aith_array_length = array => array.length;

const aith_array_literal = length => elements => {
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

const aith_util_create_child_pointer = (tuple_pointer, index) => null || {
	get: () => tuple_pointer.get()[index],
	set: object => { 
		let clone = tuple_pointer.get().slice();
		clone[index] = object;
		tuple_pointer.set(clone);
	}
};


const aith_create_pointer = _ => ([object, world]) => [{
	get: () => object,
	set: value => { object = value; }
}, undefined];

const aith_tuple_address_forword = (index,tuple_size) => tuple_pointer => {
	if(tuple_pointer.children === undefined){
		tuple_pointer.children = [];
		for(let i = 0; i < tuple_size; i++){
			tuple_pointer.children[i] = aith_util_create_child_pointer(tuple_pointer,i);
		}
	}
	return tuple_pointer.children[index]; 
};

const aith_array_address_of = ([array, index]) => {
	array.data.pointers = array.data.pointers || [];

	const pointers = array.data.pointers;
	const realIndex = array.start + index;
	pointers[realIndex] = pointers[realIndex] || {
		get: () => array.data[realIndex],
		set: object => { array.data[realIndex] = object; }
	};
	return pointers[realIndex]
};


const aith_pointer_assign = ([pointer, value]) => {
	pointer.set(value);
	return [];
};

const aith_derefence_pointer = ([pointer,_]) => {
	return [pointer.get(), undefined];
};

// logic

const aith_and = ([left,right]) => {
	return left && right;
};

const aith_or = ([left,right]) => {
	return left || right;
}

const aith_not = boolean => !boolean;


// numbers

const aith_lessthan = ([size, signed]) => ([left,right]) => {
	return left < right;
};

const aith_lessthan_equal = ([size, signed]) => ([left,right]) => {
	return left <= right;
};

const aith_greater = ([size, signed]) => ([left,right]) => {
	return left > right;
};

const aith_greater_equal = ([size, signed]) => ([left,right]) => {
	return left >= right;
};

const aith_add = ([size, signed]) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left + right | 0;
	} else if(!signed && size == 32){
		return left + right >>> 0;
	} else {
		throw "Bad number size";
	}
};

const aith_subtract = ([size, signed]) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left - right | 0;
	} else if(!signed && size == 32){
		return left - right >>> 0;
	} else {
		throw "Bad number size";
	}
};
const aith_multiply = ([size, signed]) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left * right | 0;
	} else if(!signed && size == 32){
		return left * right >>> 0;
	} else {
		throw "Bad number size";
	}
};

const aith_divide = ([size, signed]) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left / right | 0;
	} else if(!signed && size == 32){
		return left / right >>> 0;
	} else {
		throw "Bad number size";
	}
};

const aith_modulus = ([size, signed]) => ([left,right]) => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return left % right | 0;
	} else if(!signed && size == 32){
		return left % right >>> 0;
	} else {
		throw "Bad number size";
	}
};

const aith_negate = ([size, signed]) => number => {
	if(size == 0) size = 32;
	if(signed && size == 32){
		return -number | 0;
	} else if(!signed && size == 32){
		return -number >>> 0;
	} else {
		throw "Bad number size";
	}
}

const aith_cast_integer = ([input_size, input_signed], [size, signed]) => number => {
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

const aith_index_tuple = index => tuple => {
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
