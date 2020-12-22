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

const aith_create_pointer = _ => ([object, world]) => [{
	get: () => object,
	set: value => { object = value; }
}, undefined];

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
	return [[], undefined];
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

const aith_number_integer32_less = ([left,right]) => left < right;
const aith_number_integer32_greater = ([left,right]) => left > right;
const aith_number_integer32_less_equal = ([left,right]) => left <= right;
const aith_number_integer32_greater_equal = ([left,right]) => left >= right;
const aith_number_integer32_add = ([left,right]) => left + right | 0;
const aith_number_integer32_subtract = ([left,right]) => left - right | 0;
const aith_number_integer32_multiply = ([left,right]) => Math.imul(left,right);
const aith_number_integer32_divide = ([left,right]) => left / right | 0;
const aith_number_integer32_modulus = ([left,right]) => left % right | 0;
const aith_number_integer32_negate = number => -number | 0;

const aith_number_natural32_less = ([left,right]) => left < right;
const aith_number_natural32_greater = ([left,right]) => left > right;
const aith_number_natural32_less_equal = ([left,right]) => left <= right;
const aith_number_natural32_greater_equal = ([left,right]) => left >= right;
const aith_number_natural32_add = ([left,right]) => left + right >>> 0;
const aith_number_natural32_subtract = ([left,right]) => left - right >>> 0;
const aith_number_natural32_multiply = ([left,right]) => Math.imul(left,right);
const aith_number_natural32_divide = ([left,right]) => left / right >>> 0;
const aith_number_natural32_modulus = ([left,right]) => left % right >>> 0;
const aith_number_natural32_negate = number => -number >>> 0;

const aith_number_integer_less = aith_number_integer32_less;
const aith_number_integer_greater = aith_number_integer32_greater;
const aith_number_integer_less_equal = aith_number_integer32_less_equal;
const aith_number_integer_greater_equal = aith_number_integer32_greater_equal;
const aith_number_integer_add = aith_number_integer32_add;
const aith_number_integer_subtract = aith_number_integer32_subtract;
const aith_number_integer_multiply = aith_number_integer32_multiply;
const aith_number_integer_divide = aith_number_integer32_divide;
const aith_number_integer_modulus = aith_number_integer32_modulus;
const aith_number_integer_negate = aith_number_integer32_negate;

const aith_number_natural_less = aith_number_natural32_less;
const aith_number_natural_greater = aith_number_natural32_greater;
const aith_number_natural_less_equal = aith_number_natural32_less_equal;
const aith_number_natural_greater_equal = aith_number_natural32_greater_equal;
const aith_number_natural_add = aith_number_natural32_add;
const aith_number_natural_subtract = aith_number_natural32_subtract;
const aith_number_natural_multiply = aith_number_natural32_multiply;
const aith_number_natural_divide = aith_number_natural32_divide;
const aith_number_natural_modulus = aith_number_natural32_modulus;
const aith_number_natural_negate = aith_number_natural32_negate;


const aith_number_integer32 = null;
const aith_number_integer0 = null;
const aith_number_natural32 = null;
const aith_number_natural0 = null;


// tuples



const aith_util_create_child_pointer = (tuple_pointer, index) => null || {
	get: () => tuple_pointer.get()[index],
	set: object => { 
		let clone = tuple_pointer.get().slice();
		clone[index] = object;
		tuple_pointer.set(clone);
	}
};

const aith_has_tuple = (index,tuple_size) => [
	tuple => tuple[index],
	tuple_pointer => {
		if(tuple_pointer.children === undefined){
			tuple_pointer.children = [];
			for(let i = 0; i < tuple_size; i++){
				tuple_pointer.children[i] = aith_util_create_child_pointer(tuple_pointer,i);
			}
		}
		return tuple_pointer.children[index]; 
	}
];

// misc

const write = ([argument, world]) => {
	console.log(argument.data);
	return [[], undefined];
}

const assert = ([check, world]) => {
	if (!check) {
		console.trace("Error");
		throw "Assetion Error";
	}
	return [[], undefined];
}

// generated code:
