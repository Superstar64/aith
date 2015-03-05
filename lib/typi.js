/*Copyright (C) 2015  Freddy Angel Cubas "Superstar64"
 MIT License
*/
var libtypi=libtypi||{};

libtypi.array=function(length,init){
	if(length===undefined){
		length=0;
	}
	var narray=[];
	for(var i=0;i<length;i++){
		narray.push(libtypi.pointer(init));
	}
	var typiarray={};
	
	typiarray.array=narray;
	typiarray.offset=0;
	typiarray.length=narray.length;
	return typiarray;
}
libtypi.array.get=function(arr,index){
	return arr.array[arr.offset+index]();
};
libtypi.array.set=function(arr,index,value){
	return arr.array[arr.offset+index](value);
};
libtypi.array.addr=function(arr,index){
	return arr.array[arr.offset+index];
};
libtypi.array.slice=function(arr,start,end){
	var cpy=libtypi.array.copy(arr);
	cpy.offset+=start;
	cpy.length=end-start;
	return cpy;
};
libtypi.array.realloc=function(arr){
	var narray=[];
	for(var i=0;i<arr.length;i++){
		narray.push(libtypi.pointer(libtypi.array.get(arr,i)));
	}
	var nobj=libtypi.array.copy(arr);
	nobj.offset=0;
	nobj.array=narray;
	return nobj;
};
libtypi.array.concat=function(arr,value){
	var nobj=libtypi.array.realloc(arr);
	nobj.array.push(libtypi.pointer(value));
	nobj.length++;
	return nobj;
};
libtypi.array.concatArray=function(arr,arr2){
	var nobj=libtypi.array.realloc(arr);
	for(var i=0;i<arr2.length;i++){
		nobj.array.push(libtypi.pointer(libtypi.array.get(arr2,i)));
	}
	nobj.length=nobj.length+arr.length;
	return nobj;
};
libtypi.array.copy=function(arr){
	var nobj={};
	nobj.array=arr.array;
	nobj.offset=arr.offset;
	nobj.length=arr.length;
	nobj.struct=arr.struct;
	return nobj;
};
libtypi.array.literal=function(arg){
	var ret=libtypi.array(arg.length);
	for(var i=0;i<arg.length;i++){
		libtypi.array.set(ret,i,arg[i]);
	}
	return ret;
}
libtypi.struct=function(arg){
	var ret=libtypi.array.literal(arg);
	ret.struct=true;
	return ret;
}

libtypi.pointer=function(source){
	var elm=libtypi.copy(source);
	var ret=function(arg){
		if(arg===undefined){
			return elm;
		}else{
			elm=libtypi.copy(arg);
			return elm;
		}
	};
	ret.pointer=true;//rtti
	return ret;
}

//used in pass by value
libtypi.copy=function(value){
	if(typeof value=="number"||typeof value=="boolean"||typeof value=="function"||typeof value=="string"){
		return value;
	}
	if(typeof value=="object"){
		if(value.struct){
			return value.realloc;
		}
		if(value.array/*&&!value.struct*/){//it's okay to have arrays share instance,you can't change the poiner or length
			return value;
		}
	}
}

libtypi.equal=function(v1,v2){
	var type=typeof v1;
	if(type=="number"||type=="boolean"||type=="function"||type=="string"){
		return v1==v2;
	}
	if(type=="object"){
		if(v1.array){//and struct
			if(v1.length!=v2.length){
				return false;
			}
			for(var i=0;i<v1.length;i++){
				if(!libtypi.equal(libtypi.array.get(v1,i),libtypi.array.get(v2,i))){
					return false;
				}
			}
			return true;
		}
	}
}

libtypi.uint8=function(val){
	return val&0xff;
}

libtypi.uint16=function(val){
	return val&0xffff;
}

libtypi.uint32=function(val){
	return val&0xffffffff;
}

libtypi.int8=function(val){
	val=val|0;
	while(val>0x7f){
		val-=0x100;
	}
	while(-0x80>val){
		val+=0x100;
	}
	return val;
}

libtypi.int16=function(val){
	val=val|0;
	while(val>0x7f00){
		val-=0x10000;
	}
	while(-0x8000>val){
		val+=0x10000;
	}
	return val;
}

libtypi.int32=function(val){
	val=val|0;
	return val;
}

libtypi.typiStringtoJSString=function(val){
	var result="";
	for(var i=0;i<val.length;i++){
		result+=libtypi.array.get(val,i);
	}
	return result;
}

libtypi.jsStringToTypiString=function(val){
	var array=[];
	for(var i=0;i<val.length;i++){
		var cp=val.charCodeAt(i);
		if(cp>=0xD800 && cp<=0xD8FF){
			array.push(val.substring(i,i+2));
			i++;
		}else{
			array.push(val.charAt(i));
		}
	}
	return libtypi.array.literal(array);
}
