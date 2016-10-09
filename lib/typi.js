/*Copyright (C) 2015  Freddy Angel Cubas "Superstar64"
 Boost License
*/
var libtypi=libtypi||{};

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

libtypi.typiStringtoJSString=function(val){
	var result="";
	for(var i=0;i<val.length;i++){
		result += (val.array || val)[(val.start || 0) + i];
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
	return array;
}
