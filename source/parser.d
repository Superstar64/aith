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
import std.bigint: BigInt;
import std.conv: to;
import std.path: buildPath;
import std.file: read;
import std.algorithm: map,all;
template staticForeach(T...){
	alias staticForeach=T;
}

import syntax;
import error: error;
import lexer;
import etc;
/+todo:
 + add chars
 + strings / arrayliterals
 +/
@safe:
struct Loader{
	string[] importPaths;
	@trusted string open(string file){
		foreach(i;importPaths){
			try{
				auto f=cast(string)read(buildPath(i,file));
				return f;
			}catch(Throwable){
				
			}
		}
		error("Unable to open file "~file);
		return null;
	}
	
	string openImport(string[] imp){
		return open(buildPath(imp)~".typi");
	}
}

void readFiles(Loader load,string[][] files,out Module[string[]] wanted,out Module[string[]] all){
	Module readModule(string[] imp){
		auto m=imp in all;
		if(m){
			return *m;
		}
		auto parser=Parser(Lexer(imp.join("::").to!string,load.openImport(imp)),&readModule);
		auto mod=parser.parseModule;
		all[imp.idup]=mod;
		mod.namespace=imp;
		return mod;
	}
	foreach(f;files){
		wanted[f.idup]=readModule(f);
	}
}

void processModules(Module[] mods){
	foreach(m;mods){
		checkIntTypeSize(m);
	}
	foreach(m;mods){
		assignIndirectTypes(m);
	}
	foreach(m;mods){
		assignValueTypes(m);
	}
	foreach(m;mods){
		checkBranches(m);
	}
	foreach(m;mods){
		checkGlobalExec(m);
	}
}

void checkIntTypeSize(Module mod){
	void visiter(Node n,Trace t){
		void subVisit(){
			foreach(ch,subt;n.children(t)){
				visiter(ch,subt);
			}
		}
		if(cast(Int)n||cast(UInt)n){
			uint size=(cast(Int)n)?(cast(Int)n).size:(cast(UInt)n).size;
			if(size==0){
				subVisit;
				return;
			}
			uint check=1;
			while(true){
				if(check==size){
					subVisit;
					return;
				}
				if(check>size){
					error("Bad Int Size",n.pos);
				}
				check*=2;
			}
		}
		subVisit;
	}
	visiter(mod,null);
}

void assignIndirectTypes(Module mod){
	void visiter(Node e,Trace sc){
		void subVisit(){
			foreach(ch,subt;e.children(sc)){
				visiter(ch,subt);
			}
		}
		subVisit;
		if(cast(IndirectType)e){
			if(cast(SubType)e){
				auto ty=cast(SubType)e;
				auto sub=ty.type;
				if(cast(Pointer)sub){
					ty.actual_=(cast(Pointer)sub).type;
				}else{
					error("Unable to deref",e.pos);
				}
			}else if(cast(IndexType)e){
				auto ty=cast(IndexType)e;
				auto sub=ty.type;
				if(cast(Struct)sub){
					auto str=cast(Struct)sub;
					if(ty.index.peek!BigInt){
						auto ind=toUInt(ty.index.get!(BigInt));
						if(ind>=str.types.length){
							error("Index to big",e.pos);
						}
						ty.actual_=str.types[ind];
					}else{
						auto name=ty.index.get!string;
						if(name in str.names){
							auto ind=str.names[name];
							assert(ind<str.types.length);
							ty.actual_=str.types[ind];
						}else{
							error("Unknown field",e.pos);
						}
					}
				}else if(cast(Array)sub && ty.index.peek!string && (ty.index.get!string)=="length"){
					ty.actual_=new UInt(0);
				}else{
					error("Unable to get member",e.pos);
				}
			}else if(cast(UnknownType)e){
				auto ty=cast(UnknownType)e;
				auto act=sc.type(ty.name,ty.namespace);
				if(act){
					ty.actual_=act;
				}else{
					error("Unknown identifier",e.pos);
				}
			}else{
				assert(0);
			}
			auto intype=cast(IndirectType)e;
			@trusted void compare(Type actual){
				if(actual==e){
					error("self referecing type",e.pos);
				}
				if(cast(IndirectType)actual){
					compare((cast(IndirectType)actual).actual_);
				}else if(cast(Struct)actual){
					foreach(t;(cast(Struct)actual).types){
						compare(t);
					}
				}
			}
			compare(intype.actual_);
			return;
		}
	}
	visiter(mod,null);
}

void assignValueTypes(Module mod){//assigns types,lvalues,purity to values
	void delegate(ModuleVar mv) @trusted  processMVar;
	void checkVal(Value val,Trace t){
		if(cast(IntLit)val){
			if((cast(IntLit)val).usigned){
				val.type=new UInt(0);
			}else{
				val.type=new Int(0);
			}
			val.ispure=true;
			return;
		}
		if(cast(CharLit)val){
			val.type=new Char();
			val.ispure=true;
			return;
		}
		if(cast(BoolLit)val){
			val.type=new Bool();
			val.ispure=true;
			return;
		}
		if(cast(StructLit)val){
			auto st=cast(StructLit)val;
			foreach(c;st.values){
				checkVal(c,t);
			}
			auto ty=new Struct();
			ty.names=st.names;
			foreach(v;st.values){
				ty.types~=v.type;
			}
			val.type=ty;
			val.ispure=st.values.map!(a=>a.ispure).all;
			return;
		}
		if(cast(Variable)val){
			auto var=cast(Variable)val;
			auto vardef=t.var(var.name,var.namespace);
			if(vardef is null){
				error("Unable to find variable",var.pos);
			}
			if(cast(ModuleVar)vardef && (cast(ModuleVar)vardef).getType is null){
				auto mvardef=cast(ModuleVar)vardef;
				processMVar(mvardef);
			}
			assert(vardef.getType);
			val.type=vardef.getType;
			val.lvalue=!vardef.manifest;
			
			Trace fhead=t;
			while(!cast(FuncLit.FuncLitTrace)(fhead)){
				fhead=t.upper;
				if(fhead is null){
					assert(cast(ModuleVar)vardef);
					assert(val.ispure==false);
					return;
				}
			}
			auto outer=fhead.upper;
			assert(outer);
			if(t.var(var.name,var.namespace)){
				assert(val.ispure==false);
			}else{
				val.ispure=true;//val is found is function scope and not outside
			}
			return;
		}
		if(cast(If)val){
			auto iF=cast(If)val;
			checkVal(iF.cond,t);
			checkVal(iF.yes,t);
			checkVal(iF.no,t);
			if(!sameType(iF.cond.type,new Bool())){
				error("Boolean expected in if expression",iF.cond.pos);
			}
			if(!(sameType(iF.yes.type,iF.no.type)||implicitConvertInt(iF.yes,iF.no.type,t) ||implicitConvertInt(iF.no,iF.yes.type,t))){
				error("If expression with the true and false parts having different types",iF.pos);
			}
			val.type=iF.yes.type;
			val.ispure=iF.cond.ispure&&iF.yes.ispure&&iF.no.ispure;
			return;
		}
		if(cast(While)val){
			auto wh=cast(While)val;
			checkVal(wh.cond,t);
			if(!sameType(wh.cond.type,new Bool())){
				error("Boolean expected in if expression",wh.cond.pos);
			}
			checkVal(wh.state,t);
			val.type=new Struct();
			val.ispure=wh.cond.ispure&&wh.state.ispure;
			return;
		}
		if(cast(New)val){
			auto ne=cast(New)val;
			checkVal(ne.value,t);
			auto ptr=new Pointer();
			ptr.type=ne.value.type;
			val.type=ptr;
			val.ispure=ne.value.ispure;
			return;
		}
		if(cast(NewArray)val){
			auto ne=cast(NewArray)val;
			checkVal(ne.length,t);
			checkVal(ne.value,t);
			if(!(sameType(ne.length.type,new UInt(0))||implicitConvertInt(ne.length,new UInt(0),t))){
				error("Can only create an array with length of UInts",ne.length.pos);
			}
			auto ar=new Array();
			ar.type=ne.value.type;
			val.type=ar;
			val.ispure=ne.length.ispure&&ne.value.ispure;
			return;
		}
		if(cast(Cast)val){
			auto ct=cast(Cast)val;
			checkVal(ct.value,t);
			if(!castable(ct.value.type,ct.wanted)){
				error("Unable to cast",ct.pos);
			}
			val.type=ct.wanted;
			val.ispure=ct.value.ispure;
			return;
		}
		if(cast(Dot)val){
			auto dot=cast(Dot)val;
			checkVal(dot.value,t);
			if(cast(Array)(dot.value.type.actual) && dot.index.peek!string && (dot.index.get!string=="length")){
				val.type=new UInt(0);
			}else{
				if(cast(Struct)(dot.value.type.actual) is null){
					error("Unable to dot",dot.pos);
				}
				auto dval=cast(Struct)(dot.value.type.actual);
				if(dot.index.peek!string){
					auto str=dot.index.get!string;
					if(!(str in dval.names)){
						error("Unable to find field",dot.pos);
					}
					val.type=dval.types[dval.names[str]];
				}else{
					uint index=dot.index.get!(BigInt).toUInt;
					if(index>=dval.types.length){
						error("Index number to high",dot.pos);
					}
					val.type=dval.types[index];
				}
				val.lvalue=dot.value.lvalue;
			}
			val.ispure=dot.value.ispure;
			return;
		}
		
		if(cast(ArrayIndex)val){
			auto arr=cast(ArrayIndex)val;
			checkVal(arr.array,t);
			checkVal(arr.index,t);
			if(!cast(Array)(arr.array.type.actual)){
				error("Unable able to index",arr.pos);
			}
			if(!(sameType(arr.index.type,new UInt(0))||implicitConvertInt(arr.index,new UInt(0),t))){
				error("Can only index an array with UInts",arr.pos);
			}
			auto ar=cast(Array)(arr.array.type);
			val.type=ar.type;
			val.lvalue=true;
			val.ispure=arr.array.ispure&&arr.index.ispure;
			return;
		}
		
		if(cast(FCall)val){
			auto fcall=cast(FCall)val;
			checkVal(fcall.fptr,t);
			checkVal(fcall.arg,t);
			auto fn=cast(Function)(fcall.fptr.type.actual);
			if(!fn){
				error("Not a function",fcall.pos);
			}
			auto fun=cast(Function)(fcall.fptr.type.actual);
			if(!sameType(fun.arg,fcall.arg.type)){
				error("unable to call function with arg's type",fcall.pos);
			}
			val.type=fun.ret;
			val.ispure=fcall.fptr.ispure&&fn.ispure&&fcall.arg.ispure;
			return;
		}
		if(cast(Slice)val){
			auto sli=cast(Slice)val;
			checkVal(sli.array,t);
			checkVal(sli.left,t);
			checkVal(sli.right,t);
			if(!cast(Array)(sli.array.type.actual)){
				error("Not an array",sli.pos);
			}
			if(!(sameType(sli.right.type,new UInt(0))||implicitConvertInt(sli.left,new UInt(0),t))||!(sameType(sli.right.type,new UInt(0))||implicitConvertInt(sli.right,new UInt(0),t))){
				error("Can only index an array with UInts",sli.pos);
			}
			val.type=sli.array.type;
			val.ispure=sli.array.ispure&&sli.left.ispure&&sli.right.ispure;
			return;
		}
		if(cast(StringLit)val){
			auto ty=new Array;
			ty.type=new Char;
			val.type=ty;
			val.ispure=true;
			return;
		}
		if(cast(ArrayLit)val){
			auto array=cast(ArrayLit)val;
			foreach(v;array.values){
				checkVal(v,t);
			}
			if(array.values.length==0){
				error("Array Literals must contain at least one element",val.pos);
			}
			Type current=array.values[0].type;
			foreach(v;array.values[1..$]){
				if(!sameType(current,v.type)){
					error("All elements of an array literal must be of the same type",val.pos);
				}
			}
			auto ty=new Array;
			ty.type=current;
			val.type=ty;
			val.ispure=true;
			foreach(v;array.values){
				val.ispure=val.ispure&&v.ispure;
			}
			return;
		}
		
		foreach(op;staticForeach!("*","/","%","+","-","&","|","^","<<",">>",">>>")){
			if(cast(Binary!op)val){
				auto bn=cast(Binary!op)val;
				checkVal(bn.left,t);
				checkVal(bn.right,t);
				auto ty=bn.left.type;
				if(!( (cast(UInt)(ty.actual) || cast(Int)(ty.actual)) && (sameType(ty,bn.right.type) || implicitConvertInt(bn.left,bn.right.type,t)|| implicitConvertInt(bn.right,bn.left.type,t)))){
					error(op~" only works on Ints or UInts of the same Type",bn.pos);
				}
				val.type=ty;
				val.ispure=bn.left.ispure&&bn.right.ispure;
				return;
			}
		}
		
		if(cast(Binary!"~")val){
			auto bn=cast(Binary!"~")val;
			checkVal(bn.left,t);
			checkVal(bn.right,t);
			auto ty=bn.left.type;
			if(!( cast(Array)(ty.actual)  && sameType(ty,bn.right.type))){
				error("~ only works on Arrays of the same Type",bn.pos);
			}
			val.type=ty;
			val.ispure=bn.left.ispure&&bn.right.ispure;
			return;
		}
		
		foreach(op;staticForeach!("==","!=")){
			if(cast(Binary!op)val){
				auto bn=cast(Binary!op)val;
				checkVal(bn.left,t);
				checkVal(bn.right,t);
				if(!(sameType(bn.left.type,bn.right.type)||implicitConvertInt(bn.left,bn.right.type,t)||implicitConvertInt(bn.right,bn.left.type,t))){
					error(op~" only works on the same Type",bn.pos);
				}
				val.type=new Bool();
				val.ispure=bn.left.ispure&&bn.right.ispure;
				return;
			}
		}
		
		foreach(op;staticForeach!("<=",">=",">","<")){
			if(cast(Binary!op)val){
				auto bn=cast(Binary!op)val;
				checkVal(bn.left,t);
				checkVal(bn.right,t);
				auto ty=bn.left.type;
				if(!( (cast(UInt)(ty.actual) || cast(Int)(ty.actual))  && (sameType(ty,bn.right.type)||implicitConvertInt(bn.left,bn.right.type,t)||implicitConvertInt(bn.right,bn.left.type,t)))){
					error(op~" only works on Ints or UInts of the same Type",bn.pos);
				}
				val.type=new Bool();
				val.ispure=bn.left.ispure&&bn.right.ispure;
				return;
			}
		}
		
		foreach(op;staticForeach!("&&","||")){
			if(cast(Binary!op)val){
				auto bn=cast(Binary!op)val;
				checkVal(bn.left,t);
				checkVal(bn.right,t);
				auto ty=bn.left.type;
				if(!( cast(Bool)(ty.actual)  && sameType(ty,bn.right.type) )){
					error(op~" only works on Ints or UInts of the same Type",bn.pos);
				}
				val.type=new Bool();
				val.ispure=bn.left.ispure&&bn.right.ispure;
				return;
			}
		}
		
		if(cast(Binary!"=")val){
			auto bn=cast(Binary!"=") val;
			checkVal(bn.left,t);
			checkVal(bn.right,t);
			if(!(sameType(bn.left.type,bn.right.type)||implicitConvertInt(bn.right,bn.left.type,t))){
				error("= only works on the same type",bn.pos);
			}
			if(!bn.left.lvalue){
				error("= only works on lvalues",bn.pos);
			}
			val.type=bn.left.type;
			val.ispure=bn.left.ispure&&bn.right.ispure;
			return;
		}
		
		if(cast(Prefix!"-")val){
			auto bn=cast(Prefix!"-") val;
			checkVal(bn.value,t);
			if(!cast(Int)(bn.value.type.actual)){
				error("= only works on the same type",bn.pos);
			}
			val.type=bn.value.type;
			val.ispure=bn.value.ispure;
			return;
		}
		
		if(cast(Prefix!"*")val){
			auto bn=cast(Prefix!"*") val;
			checkVal(bn.value,t);
			if(!cast(Pointer)(bn.value.type.actual)){
				error("* only works on pointers",bn.pos);
			}
			val.type=(cast(Pointer)(bn.value.type.actual)).type;
			val.lvalue=true;
			val.ispure=bn.value.ispure;
			return;
		}
		
		if(cast(Prefix!"~")val){
			auto bn=cast(Prefix!"~") val;
			checkVal(bn.value,t);
			if(!(cast(UInt)(bn.value.type.actual) || cast(Int)(bn.value.type.actual))){
				error("~ only works on Ints and UInts",bn.pos);
			}
			val.type=bn.value.type;
			val.ispure=bn.value.ispure;
			return;
		}
		
		if(cast(Prefix!"&")val){
			auto bn=cast(Prefix!"&") val;
			checkVal(bn.value,t);
			if(!bn.value.lvalue){
				error("& only works lvalues",bn.pos);
			}
			void assignVar(Variable vari){//needs testing
				Var var=t.var(vari.name,vari.namespace);
				var.heap=true;
			}
			void assignDot(Dot dot){
				if(cast(Dot)(dot.value)){
					assignDot(cast(Dot)(dot.value));
				}
				if(cast(Variable)(dot.value)){
					assignVar(cast(Variable)(dot.value));
				}
			}
			if(cast(Variable)(bn.value)){
				assignVar(cast(Variable)bn.value);
			}
			
			auto ptr=new Pointer();
			ptr.type=bn.value.type;
			val.type=ptr;
			val.ispure=bn.value.ispure;
			return;
		}
		
		
		if(cast(Prefix!"!")val){
			auto bn=cast(Prefix!"!") val;
			checkVal(bn.value,t);
			if(!sameType(bn.value.type,new Bool())){
				error("! only works on Bools",bn.pos);
			}
			val.type=bn.value.type;
			val.ispure=bn.value.ispure;
			return;
		}
		
		foreach(op;staticForeach!("+","/")){
			if(cast(Prefix!op)val){
				error(op~" not supported",val.pos);
			}
		}
		
		if(cast(Scope)val){
			auto scop=cast(Scope)val;
			auto subt=scop.genTrace(t);
			val.ispure=true;
			foreach(state;scop.states){
				if(state.peek!Value){
					checkVal(state.get!Value,subt);
					val.ispure=val.ispure&&state.get!(Value).ispure;
				}else{
					auto sv=state.get!ScopeVar;
					checkVal(sv.def,subt);
					(cast(Scope.ScopeTrace)subt).vars[sv.name]=sv;
					val.ispure=val.ispure&&sv.def.ispure;
				}
			}
			if(scop.type is null){
				scop.type=new Struct();
				scop.noreturn=true;
			}
			return;
		}
		
		if(cast(FuncLit)val){
			auto func=cast(FuncLit)val;
			auto subt=func.genTrace(t);
			checkVal(func.text,subt);
			auto ftype=new Function();
			ftype.ret=func.text.type;
			ftype.arg=func.fvar.ty;
			ftype.ispure=func.text.ispure;
			val.type=ftype;
			val.ispure=true;
			return;
		}
		
		if(cast(Return)val){
			auto fn=cast(Return)val;
			checkVal(fn.value,t);
			bool max=fn.upper==uint.max;
			auto sc2=t;
			if(cast(FuncLit.FuncLitTrace)sc2){
				error("Can't return from a function literal",fn.pos);
			}
			for(uint i=0;i<fn.upper;i++){
				auto prev=sc2;
				sc2=sc2.upper;
				assert(sc2);//should never happen, scopes must be inside functions
				if(!cast(Scope.ScopeTrace)sc2){
					if(!max){
						error("passed upper scope limit",fn.pos);
					}else{
						sc2=prev;
						fn.upper=i;
						break;
					}
				}
			}
			auto sc3=cast(Scope.ScopeTrace)sc2;
			if(sc3.scop.type is null){
				sc3.scop.type=fn.value.type;
			}else{
				if(!sameType(sc3.scop.type,fn.value.type)){
					error("Doesn't match return type",fn.pos);
				}
			}
			val.type=fn.value.type;
			val.ispure=fn.value.ispure;
			return;
		}
		assert(0);
	}
	
	void processMVar_(ModuleVar mv){
		if(mv.process){
			error("forward declartion",mv.pos);
		}
		mv.process=true;
		auto trace=mod.genTrace(null);
		checkVal(mv.def,trace);
	}
	processMVar=&processMVar_;
	foreach(mv;mod.vars){
		if(!mv.process){
			processMVar(mv);
		}
	}
}
//modifys v inplace
//returns where v has been modify
bool implicitConvertInt(ref Value v,Type ty,Trace t){
	if(cast(IntLit)v && (cast(UInt)(ty.actual) || cast(Int)(ty.actual))){
		auto res=new Cast;
		res.wanted=ty;
		res.value=v;
		res.type=ty;
		v=res;
		return true;
	}
	if(cast(StructLit)v && cast(Struct)(ty.actual)){
		auto str=cast(StructLit)v;
		auto tar=cast(Struct)ty;
		foreach(c,ref val;str.values){
			if(sameType(val.type,tar.types[c])){
				continue;
			}
			if(implicitConvertInt(val,tar.types[c],t)){
				continue;
			}
			return false;
		}
		return true;
	}
	return false;
}

bool sameType(Type a,Type b){
	auto t1=a.actual;assert(t1);
	auto t2=b.actual;assert(t2);
	if(cast(Bool)t1 && cast(Bool)t2){
		return true;
	}else if(cast(Char)t1 && cast(Char)t2){
		return true;
	}else if(cast(Int)t1 && cast(Int)t2){
		return (cast(Int)t1).size==(cast(Int)t2).size;
	}else if(cast(UInt)t1 && cast(UInt)t2){
		return (cast(UInt)t1).size==(cast(UInt)t2).size;
	}else if(cast(Struct)t1 && cast(Struct)t2){
		auto s1=cast(Struct)t1;
		auto s2=cast(Struct)t2;
		if(s1.types.length!=s2.types.length){
			return false;
		}
		foreach(c,t;s1.types){
			if(!sameType(t,s2.types[c])){
				return false;
			}
		}
		return true;
	}else if(cast(Pointer)t1 && cast(Pointer)t2){
		return sameType((cast(Pointer)t1).type,(cast(Pointer)t2).type);
	}else if(cast(Array)t1 && cast(Array)t2){
		return sameType((cast(Array)t1).type,(cast(Array)t2).type);
	}else if(cast(Function)t1 && cast(Function)t2){
		return sameType((cast(Function)t1).ret,(cast(Function)t2).ret) && sameType((cast(Function)t1).arg,(cast(Function)t2).arg);
	}
	
	return false;
}

bool castable(Type tar,Type want){
	tar=tar.actual;
	want=want.actual;
	if(sameType(tar,want)){
		return true;
	}
	if(sameType(tar,new Struct())){
		return true;
	}
	if((cast(Int)tar || cast(UInt)tar) && (cast(Int)want || cast(UInt)want)){//casting between int types
		return true;
	}
	return false;
}

void checkBranches(Module m){
	@trusted bool Returns(Value v,uint level){
		if(cast(CharLit)v||cast(IntLit)v||cast(BoolLit)v||cast(Variable)v||cast(StringLit)v){
			return false;
		}
		if(cast(StructLit)v){
			auto sl=cast(StructLit)v;
			foreach(val;sl.values){
				if(Returns(val,level)){
					return true;
				}
			}
			return false;
		}
		if(cast(If)v){
			auto iF=cast(If)v;
			return Returns(iF.cond,level) || (Returns(iF.yes,level) && Returns(iF.no,level));
		}
		if(cast(While)v){
			auto wh=cast(While)v;
			return Returns(wh.cond,level);
		}
		if(cast(New)v){
			auto ne=cast(New)v;
			return Returns(ne.value,level);
		}
		if(cast(NewArray)v){
			auto ne=cast(NewArray)v;
			return Returns(ne.length,level)|| Returns(ne.value,level);
		}
		if(cast(Cast)v){
			auto ca=cast(Cast)v;
			return Returns(ca.value,level);
		}
		if(cast(Dot)v){
			auto dot=cast(Dot)v;
			return Returns(dot.value,level);
		}
		if(cast(ArrayIndex)v){
			auto ar=cast(ArrayIndex)v;
			return Returns(ar.array,level)|| Returns(ar.index,level);
		}
		if(cast(FCall)v){
			auto fc=cast(FCall)v;
			return Returns(fc.fptr,level)||Returns(fc.arg,level);
		}
		if(cast(Slice)v){
			auto sc=cast(Slice)v;
			return Returns(sc.array,level)||Returns(sc.left,level)||Returns(sc.right,level);
		}
		if(cast(ArrayLit)v){
			auto array=cast(ArrayLit)v;
			foreach(val;array.values){
				if(Returns(val,level)){
					return true;
				}
			}
			return false;
		}
		foreach(o;staticForeach!("*","/","%","+","-","~","&","|","^","<<",">>",">>>","==","!=","<=",">=","<",">","&&","||","=")){
			if(cast(Binary!o)v){
				auto bin=cast(Binary!o)v;
				return Returns(bin.left,level)||Returns(bin.right,level);
			}
		}
		foreach(o;staticForeach!("+","-","*","/","&","~","!")){
			if(cast(Prefix!o)v){
				auto pre=cast(Prefix!o)v;
				return Returns(pre.value,level);
			}
		}
		if(cast(Scope)v){
			level++;
			foreach(sta;(cast(Scope)v).states){
				if(sta.peek!Value){
					if(Returns(sta.get!Value,level)){
						return true;
					}
				}else{
					if(Returns((sta.get!(ScopeVar)).def,level)){
						return true;
					}
				}
			}
			return false;
		}
		if(cast(FuncLit)v){
			return false;
		}
		if(cast(Return)v){
			auto fn=cast(Return)v;
			if(fn.upper==level){
				return true;
			}
			return false;
		}
		assert(0);
	}
	void visiter(Node n,Trace t){
		foreach(ch,subt;n.children(t)){
			visiter(ch,subt);
		}
		if(cast(Scope)n){
			auto sc=cast(Scope)n;
			if(sc.noreturn){
				return;
			}
			foreach(state;sc.states){
				if(state.peek!Value){
					if(Returns(state.get!Value,0)){
						return;
					}
				}else{
					if(Returns((state.get!ScopeVar).def,0)){
						return;
					}
				}
			}
			error("Missing Returns in scope",n.pos);
		}
	}
	visiter(m,null);
}

void checkGlobalExec(Module m){
	foreach(var;m.vars){
		if(!var.def.ispure){
			error("Impure expression in global",var.pos);
		}
	}
}
@trusted unittest{
	import syntax;
	auto l=Loader(["test/parser"]);
	Module[string[]] all;
	Module[string[]] wanted;
	readFiles(l,[["test"]],wanted,all);
	assert(wanted.length==1);//imports
	assert(all.length==2);
	assert(["test"] in wanted);
	assert(["subdir","file"] in all);
	assert(["test"] in all);
	assert(wanted[["test"]].imports[0]==all[["subdir","file"]]);
	
	processModules(all.values);
	
	auto test=wanted[["test"]];//assign types
	
	{
		auto test1=test.aliases["test1"];
		assert(cast(Int)test1.actual);
		auto test2=test.aliases["test2"];
		assert(cast(UInt)test2.actual);
		auto test3=test.aliases["test3"];
		assert(cast(UInt)test3.actual);
		auto test4=test.aliases["test4"];
		assert(cast(Int)test4.actual);
	}
	@trusted void vis(Node n,Trace t){import std.stdio;import error;import std.conv;
		if(cast(Value)n){
			auto val=cast(Value)n;
			assert(val.type,prettyPrint(val.pos));
			//writeln("Value "~val.to!string~" of "~val.type.to!string~" lvalue "~val.lvalue.to!string~" "~prettyPrint(val.pos));
		}
		foreach(ch,subt;n.children(t)){
			vis(ch,subt);
		}
	}
	vis(test,null);
}


@trusted unittest{
	assert(sameType(new Bool(),new Bool()));
	Type ty=new Bool();
	assert(sameType(ty,ty));
	auto st=new Struct();
	st.types~=new Int(0);
	st.types~=new Bool();
	assert(!sameType(st,new Int(0)));
	auto st2=new Struct();
	st2.types~=new Int(0);
	st2.types~=new Bool();
	assert(sameType(st,st2));
	auto ptr=new Pointer();
	ptr.type=st;
	auto ptr2=new Pointer();
	ptr2.type=st2;
	assert(sameType(ptr,ptr2));
}
