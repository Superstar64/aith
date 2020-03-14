//comparing

const typi_compare_vanilla = (left, right) => left === right;

const typi_array_compare = compare => (left, right) => {
	if (left.length != right.length) {
		return false;
	}
	for (let i = 0; i < left.length; i++) {
		if (!compare(left.data[left.start + i], right.data[right.start + i])) {
			return false;
		}
	}
	return true;
};

const typi_tuple_compare = subcompares => (left,right) => {
	for (let i = 0; i < subcompares.length; i++) {
		if (!subcompares[i](left[i], right[i])) {
			return false;
		}
	}
	return true;
};

//arrays

const typi_new_array = (length, element) => {
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

const typi_index_array = (array, index) => array.data[array.start + index];

const typi_array_slice = (array, start, end) => null || {
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


const typi_create_pointer = object => null || {
	get: () => object,
	set: value => { object = value; }
};

const typi_tuple_address_forword = tuple_size => (tuple_pointer, index) => {
	if(tuple_pointer.children === undefined){
		tuple_pointer.children = [];
		for(let i = 0; i < tuple_size; i++){
			tuple_pointer.children[i] = typi_util_create_child_pointer(tuple_pointer,i);
		}
	}
	return tuple_pointer.children[index]; 
};

const typi_array_address_of = (array, index) => {
	array.data.pointers = array.data.pointers || [];

	const pointers = array.data.pointers;
	const realIndex = array.start + index;
	pointers[realIndex] = pointers[realIndex] || {
		get: () => array.data[realIndex],
		set: object => { array.data[realIndex] = object; }
	};
	return pointers[realIndex];
};


const typi_pointer_assign = (pointer, value) => {
	return pointer.set(value);
};

const typi_derefence_pointer = pointer => {
	return pointer.get();
};

// misc

const write = argument => {
	console.log(argument.data);
}

const assert = check => {
	if (!check) {
		console.trace("Error");
		throw "Assetion Error";
	}
}

// generated code:
