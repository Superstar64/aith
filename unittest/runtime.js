var write = function(arg){
	console.log(arg);
}

var assert = function(check){
	if(!check){
		console.trace("Error");
		throw "Assetion Error";
	}
}

main([]);
