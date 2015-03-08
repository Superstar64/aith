/+Copyright (C) 2015  Freddy Angel Cubas "Superstar64"

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, version 3 of the License.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
+/
import std.array: join;
import std.stdio: write;
import std.conv: to;
import std.bigint: BigInt;
import std.algorithm: map;
import std.utf:encode;

import syntax;
import error;
import parser;

@safe:
string genJS(Module[] mods,string jsname="typi"){
	string result="/*plese include typi.js before this file*/";
	result~="var "~jsname~"="~jsname~" || {};";
	jsname~=".";
	uint uuid;
	foreach(m;mods){
		auto name=m.namespace;
		foreach(c,_;name){
			result~=jsname~name[0..c+1].join(".")~"="~jsname~name[0..c+1].join(".")~" || {};";
		}
		foreach(v;m.vars){
			result~=jsname~m.namespace.join(".")~"."~v.name~"="~genVal(v.def,jsname,m.genTrace(null),uuid,ScopeNames(),result)~";";
		}
	}
	return result;
}
@trusted string IntLitToString(IntLit i){
	return i.value.to!string;
}


struct ScopeNames{
	string[] results;
	string[] breaks;
}

//returns js expression, may append statements to result
string genVal(Value v,string jsname,Trace t,ref uint uuid,ScopeNames scopenames,ref string result){
	string genName(){
		auto vname="$"~uuid.to!string;
		uuid++;
		return vname;
	}
	if(cast(IntLit)v){
		return IntLitToString(cast(IntLit)v);
	}
	if(cast(BoolLit)v){
		auto blit=cast(BoolLit)v;
		if(blit.yes){
			return "true";
		}else{
			return "false";
		}
	}
	if(cast(CharLit)v){
		auto clit=cast(CharLit)v;
		return '"'~escape(clit.value)~'"';
	}
	if(cast(StructLit)v){
		auto slit=cast(StructLit)v;
		string[] vars;
		foreach(val;slit.values){
			vars~=genVal(val,jsname,t,uuid,scopenames,result);
		}
		return "libtypi.struct(["~vars.join(",")~"])";
	}
	if(cast(Variable)v){
		auto var=cast(Variable)v;
		Trace tt;
		auto src=t.var(var.name,var.namespace,tt);
		assert(src);
		string postfix="";
		if(src.heap){
			postfix="()";
		}
		if(cast(ModuleVar)src){
			return jsname~(cast(Module.ModuleTrace)tt).m.namespace.join(".")~"."~var.name~postfix;
		}else{
			assert(var.namespace is null);
			return var.name~postfix;
		}
	}
	if(cast(If)v){
		auto iF=cast(If)v;
		auto vname=genName();
		result~="var "~vname~" = undefined;";
		auto cond=genVal(iF.cond,jsname,t,uuid,scopenames,result);
		result~="if("~cond~") {";
		auto yes=genVal(iF.yes,jsname,t,uuid,scopenames,result);
		result~=vname~"="~yes~";";
		result~="}else{";
		auto no=genVal(iF.no,jsname,t,uuid,scopenames,result);
		result~=vname~"="~no~";}";
		return vname;
	}
	if(cast(While)v){
		auto wh=cast(While)v;
		result~="do{";
		auto cond=genVal(wh.cond,jsname,t,uuid,scopenames,result);
		result~="if(!"~cond~"){break;}";
		result~=genVal(wh.state,jsname,t,uuid,scopenames,result)~";";
		result~="}while(true);";
		return "libtypi.struct([])";
	}
	if(cast(New)v){
		auto n=cast(New)v;
		auto value=genVal(n.value,jsname,t,uuid,scopenames,result);
		return "libtypi.pointer("~value~")";
	}
	if(cast(NewArray)v){
		auto na=cast(NewArray)v;
		auto length=genVal(na.length,jsname,t,uuid,scopenames,result);
		auto value=genVal(na.value,jsname,t,uuid,scopenames,result);
		return "libtypi.array("~length~","~value~")";
	}
	if(cast(Cast)v){
		auto ca=cast(Cast)v;
		auto var=genVal(ca.value,jsname,t,uuid,scopenames,result);
		if(sameType(ca.value.type,ca.wanted)){
			return var;
		}
		if(sameType(ca.value.type,new Struct())){
			return defaultValue(ca.wanted);
		}
		if(cast(UInt) (ca.value.type.actual) || cast(Int) (ca.value.type.actual)){
			auto str=libtypiToInt(ca.wanted.actual);
			if(str){
				return str~"("~var~")";
			}
		}
		assert(0);
	}
	if(cast(Dot)v){
		auto dot=cast(Dot)v;
		auto str=genVal(dot.value,jsname,t,uuid,scopenames,result);
		@trusted string tmp(){//bigint isn't safe
			return (dot.index.get!BigInt).to!string;
		}
		if(dot.index.peek!string){
			return "libtypi.array.get("~str~","~(cast(Struct)(dot.value.type.actual)).names[dot.index.get!string].to!string~")";
		}else{
			return "libtypi.array.get("~str~","~tmp~")";
		}
	}
	if(cast(ArrayIndex)v){
		auto arin=cast(ArrayIndex)v;
		auto array=genVal(arin.array,jsname,t,uuid,scopenames,result);
		auto index=genVal(arin.index,jsname,t,uuid,scopenames,result);
		return "libtypi.array.get("~array~","~index~")";
	}
	if(cast(FCall)v){
		auto fc=cast(FCall)v;
		auto fptr=genVal(fc.fptr,jsname,t,uuid,scopenames,result);
		auto arg=genVal(fc.arg,jsname,t,uuid,scopenames,result);
		return fptr~"(libtypi.copy("~arg~"))";
	}
	if(cast(Slice)v){
		auto sli=cast(Slice)v;
		auto array=genVal(sli.array,jsname,t,uuid,scopenames,result);
		auto left=genVal(sli.left,jsname,t,uuid,scopenames,result);
		auto right=genVal(sli.right,jsname,t,uuid,scopenames,result);
		return "libtypi.array.slice("~array~","~left~","~right~")";
	}
	if(cast(StringLit)v){
		auto str=cast(StringLit)v;
		string res;
		foreach(ch;str.str){
			res~=escape(ch);
		}
		return "libtypi.jsStringToTypiString(\""~res~"\")";
	}
	if(cast(ArrayLit)v){
		auto array=cast(ArrayLit)v;
		string[] elms;
		foreach(val;array.values){
			elms~=genVal(val,jsname,t,uuid,scopenames,result);
		}
		return "libtypi.array.literal(["~elms.join(",")~"])";
	}
	foreach(o;staticForeach!("*","/","%","+","-","|","^","<<",">>",">>>")){
		if(cast(Binary!o)v){
			auto bin=cast(Binary!o)v;
			auto left=genVal(bin.left,jsname,t,uuid,scopenames,result);
			auto right=genVal(bin.right,jsname,t,uuid,scopenames,result);
			return "("~libtypiToInt(bin.type.actual)~"("~left~o~right~"))";
		}
	}
	foreach(o;staticForeach!("<=",">=","<",">","&&","||")){
		if(cast(Binary!o)v){
			auto bin=cast(Binary!o)v;
			auto left=genVal(bin.left,jsname,t,uuid,scopenames,result);
			auto right=genVal(bin.right,jsname,t,uuid,scopenames,result);
			return "("~left~o~right~")";
		}
	}
	if(cast(Binary!"==")v){
		auto bin=cast(Binary!"==")v;
		auto left=genVal(bin.left,jsname,t,uuid,scopenames,result);
		auto right=genVal(bin.right,jsname,t,uuid,scopenames,result);
		return "libtypi.equal("~left~","~right~")";
	}
	if(cast(Binary!"!=")v){
		auto bin=cast(Binary!"!=")v;
		auto left=genVal(bin.left,jsname,t,uuid,scopenames,result);
		auto right=genVal(bin.right,jsname,t,uuid,scopenames,result);
		return "!libtypi.equal("~left~","~right~")";
	}
	if(cast(Binary!"=")v){
		auto bin=cast(Binary!"=")v;
		auto right="libtypi.copy("~genVal(bin.right,jsname,t,uuid,scopenames,result)~")";
		return genValAssign(bin.left,right,jsname,t,uuid,scopenames,result);
	}
	if(cast(Binary!"~")v){
		auto bin=cast(Binary!"~")v;
		auto left=genVal(bin.left,jsname,t,uuid,scopenames,result);
		auto right=genVal(bin.right,jsname,t,uuid,scopenames,result);
		return "libtypi.array.concatArray("~left~","~right~")";
	}
	foreach(o;staticForeach!("-","~","!")){
		if(cast(Prefix!o)v){
			auto pre=cast(Prefix!o)v;
			auto sub=genVal(pre.value,jsname,t,uuid,scopenames,result);
			return o~sub;
		}
	}
	if(cast(Prefix!"&")v){
		auto pre=cast(Prefix!"&")v;
		auto sub=pre.value;
		if(cast(Variable)sub){
			auto var=cast(Variable)sub;
			Trace tt;
			auto src=t.var(var.name,var.namespace,tt);
			if(cast(ModuleVar)src){
				return jsname~(cast(Module.ModuleTrace)tt).m.namespace.join(".")~var.name;
			}else{
				return var.name;
			}
		}
		if(cast(Dot)sub){
			auto dot=cast(Dot)sub;
			auto stru=dot.value;
			assert(cast(Struct)stru.type.actual);
			string index;
			@trusted string tmp2(){//bigint isn't safe
				return (dot.index.get!BigInt).to!string;
			}
			if(dot.index.peek!string){
				index=(cast(Struct)(dot.value.type.actual)).names[dot.index.get!string].to!string;
			}else{
				index=tmp2;
			}
			auto stval=genVal(stru,jsname,t,uuid,scopenames,result);
			return "libtypi.offsetPointer("~stval~","~index~")";
		}
		if(cast(ArrayIndex)sub){
			auto arrind=cast(ArrayIndex)sub;
			auto arr=genVal(arrind.array,jsname,t,uuid,scopenames,result);
			auto index=genVal(arrind.index,jsname,t,uuid,scopenames,result);
			return "libtypi.array.addr("~arr~","~index~")";
		}
		if(cast(Prefix!"*")sub){
			auto def=cast(Prefix!"*")sub;
			return genVal(def.value,jsname,t,uuid,scopenames,result);
		}
		assert(0);
	}
	
	if(cast(Scope)v){
		auto sc=cast(Scope)v;
		auto subt=sc.genTrace(t);
		auto res=genName();
		auto breaker=genName();
		result~="var "~res~" = undefined;";
		result~=breaker~": {";
		auto scopeN=scopenames;
		scopeN.results~=res;
		scopeN.breaks~=breaker;
		foreach(state;sc.states){
			if(state.peek!Value){
				result~=genVal(state.get!Value,jsname,subt,uuid,scopeN,result)~";";
			}else{
				auto va=state.get!ScopeVar;
				string pre;
				string pos;
				if(va.heap){
					pre="libtypi.pointer(";
					pos=")";
				}
				result~="var "~va.name~" ="~pre~genVal(va.def,jsname,subt,uuid,scopeN,result)~pos~";";
				(cast(Scope.ScopeTrace)(subt)).vars[va.name]=va;
			}
		}
		result~="}";
		return res;
	}
	
	if(cast(FuncLit)v){
		auto flit=cast(FuncLit)v;
		auto subt=flit.genTrace(t);
		auto returns="function("~flit.fvar.name~"){";
		auto val=genVal(flit.text,jsname,subt,uuid,scopenames,/+special case +/returns);
		returns~="return "~val~";}";
		return returns;
	}
	
	if(cast(Return)v){
		auto ret=cast(Return)v;
		auto val=genVal(ret.value,jsname,t,uuid,scopenames,result);
		string rbreak;
		string rresult;
		if(ret.upper==uint.max){
			rbreak=scopenames.breaks[0];
			rresult=scopenames.results[0];
		}else{
			rbreak=scopenames.breaks[$-1-ret.upper];
			rresult=scopenames.results[$-1-ret.upper];
		}
		result~=rresult~"=libtypi.copy("~val~");";
		result~="break "~rbreak~";";
		return "undefined";//it doesn't matter what i return
	}
	assert(0);
}

string genValAssign(Value v,string assigner,string jsname,Trace t,uint uuid,ScopeNames scopenames,ref string result){
	if(cast(Variable)v){
			auto var=cast(Variable)v;
			Trace tt;
			auto vsrc=t.var(var.name,var.namespace,tt);
			string prefix;
			if(cast(ModuleVar)vsrc){
				prefix=jsname~(cast(Module.ModuleTrace)(tt)).m.namespace.join(".")~".";
			}
			prefix~=var.name;
			if(vsrc.heap){
				return "("~prefix~"("~assigner~"))";
			}else{
				return "("~prefix~"="~assigner~")";
			}
	}
	if(cast(Dot)v){
		auto dot=cast(Dot)v;
		auto str=genVal(dot.value,jsname,t,uuid,scopenames,result);
		@trusted string tmp(){//bigint isn't safe
			return (dot.index.get!BigInt).to!string;
		}
		if(dot.index.peek!string){
			return "libtypi.array.set("~str~","~(cast(Struct)(dot.value.type.actual)).names[dot.index.get!string].to!string~","~assigner~")";
		}else{
			return "libtypi.array.set("~str~","~tmp~","~assigner~")";
		}
	}
	if(cast(ArrayIndex)v){
		auto arin=cast(ArrayIndex)v;
		auto array=genVal(arin.array,jsname,t,uuid,scopenames,result);
		auto index=genVal(arin.index,jsname,t,uuid,scopenames,result);
		return "libtypi.array.set("~array~","~index~","~assigner~")";
	}
	if(cast(Prefix!"*")v){
		auto pre=cast(Prefix!"*")v;
		auto sub=genVal(pre.value,jsname,t,uuid,scopenames,result);
		return sub~"("~assigner~")";
	}
	assert(0);
}

string escape(dchar d){
	if(d=='\0'){
		return "\\0";//"\0" in js
	}else if(d=='\''){
		return "'";
	}else if(d=='"'){
		return "\\""";//"\"" in js
	}
	return d.to!string;
}

string libtypiToInt(Type t){
	if(cast(Int)t){
		auto i=cast(Int)t;
		if(i.size==1){
			return "libtypi.int8";
		}
		if(i.size==2){
			return "libtypi.int16";
		}
		if(i.size==0||i.size==4){
			return "libtypi.int32";
		}
	}
	if(cast(UInt)t){
		auto i=cast(UInt)t;
		if(i.size==1){
			return "libtypi.uint8";
		}
		if(i.size==2){
			return "libtypi.uint16";
		}
		if(i.size==0||i.size==4){
			return "libtypi.uint32";
		}
	}
	return null;
}

string defaultValue(Type t){
	t=t.actual;
	if(cast(Int)t||cast(UInt)t){
		return "0";
	}
	if(cast(Struct)t){
		auto st=cast(Struct)t;
		auto res="libtypi.struct([";
		foreach(c,ty;st.types){
			res~=defaultValue(ty.actual);
			if(c!=st.types.length-1){
				res~=",";
			}
		}
		res~="])";
		return res;
	}
	if(cast(Pointer)t||cast(Function)t){
		return "undefined";
	}
	if(cast(Array)t){
		return "libtypi.array(0,undefined)";
	}
	assert(0);
}

@trusted unittest{
	import std.stdio;
	import parser;
	auto l=Loader(["test/codegen"]);
	Module[string[]] all;
	Module[string[]] wanted;
	readFiles(l,[["main"]],wanted,all);
	processModules(all.values);
	auto val=genJS(all.values);
	writeln(val);
}
