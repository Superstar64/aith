
// utililty

var tagged = function(name,value){
	return {
		name : name,
		value : value
	};
};

var match = function(union,matches){
	return matches[union.name](union.value);
};

//runtime typi info

var typi_type_int = function(signed, size){
	return tagged("number",[signed,size]);
};

var typi_type_char = tagged("character",[]);

var typi_type_bool = tagged("bool",[]);

var typi_type_tuple = function(types){
	return tagged("tuple",types);
};

var typi_type_array = function(value){
	return tagged("array",value);
};

var typi_type_pointer = function(value){
	return tagged("pointer",value);
};

var typi_type_function = function(argument,result){
	return tagged("arrow",[argument,result]);
};

// type utility

var typi_assign = function(type, current, index, value){
	match(type, {
		number : function(x) { current[index] = value; },
		character : function(x) { current[index] = value; },
		bool : function(x) { current[index] = value; },
		tuple : function(subtypes) {
			for(var i = 0; i < subtypes.length;i++){
				var subtype = subtypes[i];
				current[index] = current[index] || [];
				typi_assign(subtype,current[index], i, value[i]);
			}
		},
		array : function(x) { current[index] = value; },
		pointer :  function(x) { current[index] = value; },
		arrow :  function(x) { current[index] = value; }
	});
};

//comparing

var typi_compare = function(type){
	var vanilla = function(left,right) {
		return left == right;
	};
	return match(type,{
		number : function(x) { return vanilla },
		character : function(x) { return vanilla },
		bool : function(x) { return vanilla },
		tuple : function(subtypes) {
			return function(left,right){
				for(var i = 0;i < subtypes.length; i++){
					var subtype = subtypes[i];
					if(!typi_compare(subtype)(left[i],right[i])){
						return false;
					}
				}
				return true;
			};
		},
		array : function(subtype){
			return function(left,right){
				if(left.length != right.length){
					return false;
				}
				for(var i = 0; i < left.length; i++){
					if(!typi_compare(subtype)(left.data[left.start + i],right.data[right.start + i])){
						return false;
					}
				}
				return true;
			};
		},
		pointer : function(subtype){
			return function(left,right){
				if(left.source != right.source){
					return false;
				}
				if(left.tree.length != right.tree.length){
					return false;
				}
				for(var i = 0;i < left.tree.length; i++){
					if(left.tree[i] != right.tree[i]){
						return false;
					}
				}
				return true;
			};
		},
		arrow : function (x){
			throw "comparing functions"
		}
	});
};

//arrays

var typi_new_array = function(type){
	return function(length,element){
		var fresh = [];
		for(var i = 0; i < length; i++){
			typi_assign(type, fresh, i, element);
		}
		return {
			data : fresh,
			start : 0,
			length : length
		};
	};
};

var typi_index_array = function(array,index){
	return array.data[array.start + index];
};

var typi_array_slice = function(array,start,end){
	return {
		data : array.data,
		start : array.start + start,
		length : end - start
	};
};

var typi_array_length = function(array) {
	return array.length;
};


var typi_array_literal = function(type,length){
	return function(elements){
		var fresh = [];
		for(var i = 0; i < length; i++){
			typi_assign(type, fresh, i, elements[i]);
		}
		return {
			data : fresh,
			start : 0,
			length : length
		};
	};
};

//pointers

var typi_tuple_address_forword = function(tuple_pointer, index){
	return {
		origin : tuple_pointer.origin,
		tree : tuple_pointer.tree.concat([index])
	};
};

var typi_array_address_of = function(array, index) {
    return {
    	origin : array.data,
    	tree : [array.start + index]
    };
};

var typi_pointer_assign = function(type){
	return function(pointer, value){
		var current = pointer.origin;
		for(var i = 0;i < pointer.tree.length - 1;i++){
			current = current[pointer.tree[i]];
		}
		typi_assign(type, current, pointer.tree[pointer.tree.length-1], value);
	};
};
var typi_create_pointer = function(value){
	return {
		origin : { value : value },
		tree : ["value"]
	};
};

var typi_derefence_pointer = function(pointer){
	var current = pointer.origin;
	for(var i = 0;i < pointer.tree.length;i++){
		current = current[pointer.tree[i]];
	}
	return current;
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

main();
