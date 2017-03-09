/+
	This file is part of Typi.

	Typi is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation version 3 of the License.

	Typi is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with Typi.  If not, see <http://www.gnu.org/licenses/>.
+/
module codegen;
import std.array : join;
import std.stdio : write;
import std.conv : to;
import std.bigint : BigInt;
import std.algorithm : map;
import std.utf : encode;
import std.range;
import std.algorithm;
import std.typecons : Tuple, tuple;

import ast;
import error : error;
import semantic;
import jsast;

string genJS(Module[] mods, string jsname = "") {
	JsState[] result;

	foreach (m; mods) {
		auto name = m.namespace;
		JsExpr var;
		foreach (c, _; name) {
			if (c == 0 && jsname == "") {
				result ~= new JsVarDef(name[0], new JsBinary!"||"(new JsLit(name[0]),
					new JsObject()));
				var = new JsLit(name[0]);
			} else {
				auto namespace = only(jsname).chain(name[0 .. c + 1]);
				var = new JsLit(namespace.front);
				namespace.popFront;
				foreach (n; namespace) {
					var = new JsDot(var, n);
				}
				result ~= new JsBinary!"="(var, new JsBinary!"||"(var, new JsObject()));
			}
		}
		foreach (v; m.vars) {
			Generator gen;
			result ~= new JsBinary!"="(new JsDot(var, v.name), gen.genVal(v.def,
				m.genTrace(null), gen.Usage.once, result));
		}
	}
	return "/* generated code */\n" ~ stringCode(result);
}

string intLitToString(IntLit i) {
	return i.value.to!string;
}

//structs are repesented as native arrays
//arrays are either a native array or an object with a data, start, length, 
//pointers are arrays
//functions are native js functions
struct Generator {
	uint uuid;
	Tuple!(JsLabel, string)[] scopeStack;

	string genName() {
		auto vname = "$" ~ uuid.to!string;
		uuid++;
		return vname;
	}

	enum Unique {
		no,
		copy,
		same
	};
	enum Eval {
		once,
		any,
		none
	};

	//the expression usage for genVal
	struct Usage {
		//if copy the value returned by the expression should have no aliases
		//if no any value my be returned
		//if same the same reference must be returned each evaluatation
		Unique unique;
		//should the expression cache side effects in the depend array
		//if any then the result will be evaluated 0..n times
		//if once then the result will be evaluated once
		//if none then null must be returned
		Eval cache;
		//special case when cache and unique is false
		//if null is return the sub expression wrote the value to
		//a variable called share
		//otherwise normal behavior
		JsExpr share;
		invariant() {
			if (share) {
				assert(unique == Unique.no);
				assert(cache == Eval.once);
			}
		}

	static:
		Usage container(Usage usage) {
			return Usage(Unique.copy, usage.cache);
		}

		Usage expression(Usage usage) {
			return Usage(usage.unique, usage.cache);
		}

		Usage literal() {
			return Usage(Unique.copy, Eval.any);
		}

		Usage variable() {
			return Usage(Unique.same, Eval.any);
		}

		Usage shareUsage(JsExpr share) {
			return Usage(Unique.no, Eval.once, share);
		}

		Usage once() {
			return Usage(Unique.no, Eval.once);
		}

		Usage none() {
			return Usage(Unique.no, Eval.none);
		}

		Usage copy() {
			return Usage(Unique.copy, Eval.any);
		}
	}

	JsExpr indexStruct(JsExpr str, size_t index) {
		return new JsIndex(str, new JsLit(index.to!string));
	}

	JsExpr internalArray(JsExpr array) {
		return new JsBinary!"||"(new JsDot(array, "data"), array);
	}

	JsExpr arrayStart(JsExpr array) {
		return new JsBinary!"||"(new JsDot(array, "start"), new JsLit("0"));
	}

	JsExpr arrayLength(JsExpr array) {
		return new JsDot(array, "length");
	}

	JsExpr indexArray(JsExpr array, JsExpr index) {
		return new JsIndex(internalArray(array),
			new JsBinary!"+"(new JsBinary!"||"(new JsDot(array, "start"), new JsLit("0")),
			index));
	}

	JsExpr indexPointer(JsExpr pointer) {
		return new JsIndex(internalArray(pointer),
			new JsBinary!"||"(new JsDot(pointer, "start"), new JsLit("0")));
	}

	JsExpr copy(JsExpr expr, Type type) {
		type = type.actual;
		if (cast(Bool) type || cast(Char) type || cast(Int) type || cast(UInt) type
				|| cast(Pointer) type || cast(Array) type || cast(Function) type) {
			return expr;
		} else if (auto str = cast(Struct) type) {
			auto ret = new JsArray();
			foreach (c, e; str.types) {
				ret.exprs ~= copy(indexStruct(expr, c), e);
			}
			return ret;
		} else {
			assert(0);
		}
	}

	JsExpr onceCopy(JsExpr expr, Type type, JsState[] depend) {
		type = type.actual;
		if (cast(Bool) type || cast(Char) type || cast(Int) type || cast(UInt) type
				|| cast(Pointer) type || cast(Array) type || cast(Function) type) {
			return expr;
		} else if (auto str = cast(Struct) type) {
			auto ret = genTmp(null, expr, depend);
			return copy(ret, type);
		} else {
			assert(0);
		}
	}

	JsExpr defaultValue(Type type) {
		type = type.actual;
		if (cast(UInt) type || cast(Int) type) {
			return new JsLit("0");
		} else if (cast(Bool) type) {
			return new JsLit("false");
		} else if (cast(Char) type) {
			return new JsLit('"' ~ "\\0" ~ '"');
		} else if (auto stu = cast(Struct) type) {
			auto ret = new JsArray();
			foreach (sub; stu.types) {
				ret.exprs ~= defaultValue(sub);
			}
			return ret;
		} else if (cast(Pointer) type || cast(Function) type) {
			return new JsLit("undefined");
		} else if (cast(Array) type) {
			return new JsArray();
		} else {
			assert(0);
		}
	}

	JsExpr castInt(JsExpr expr, Type type) {
		type = type.actual;
		if (auto i = cast(Int) type) {
			if (i.size == 1) {
				error("todo support size" ~ i.size.to!string);
				assert(0);
			} else if (i.size == 2) {
				error("todo support size" ~ i.size.to!string);
				assert(0);
			} else if (i.size == 4 || i.size == 0) {
				return new JsBinary!"|"(expr, new JsLit("0"));
			} else {
				error("todo support size" ~ i.size.to!string);
				assert(0);
			}
		} else if (auto i = cast(UInt) type) {
			if (i.size == 1) {
				return new JsBinary!"&"(expr, new JsLit("0xff"));
			} else if (i.size == 2) {
				return new JsBinary!"&"(expr, new JsLit("0xffff"));
			} else if (i.size == 4 || i.size == 0) {
				return new JsBinary!"&"(expr, new JsLit("0xffffffff"));
			} else {
				error("todo support size" ~ i.size.to!string);
				assert(0);
			}
		} else {
			assert(0);
		}
	}

	JsExpr compare(JsExpr left, JsExpr right, Type type, JsState[] depend) {
		type = type.actual;
		if (cast(Bool) type || cast(Char) type || cast(Int) type
				|| cast(UInt) type || cast(Function) type) {
			return new JsBinary!"=="(left, right);
		} else if (auto ptr = cast(Pointer) type) {
			return new JsBinary!"&&"(new JsBinary!"=="(internalArray(left),
				internalArray(right)), new JsBinary!"=="(arrayStart(left), arrayStart(right)));
		} else if (auto arr = cast(Array) type) {
			auto var = genName();
			auto varLit = new JsLit(var);
			depend ~= new JsVarDef(var, new JsBinary!"=="(arrayLength(left), arrayLength(right)));
			auto i = new JsLit(genName());
			auto loop = new JsFor(new JsVarDef(i.value, new JsLit("0")),
				new JsBinary!"<"(i, arrayLength(left)), new JsPostfix!"++"(i), []);
			depend ~= new JsIf(varLit, [loop], null);
			loop.states ~= new JsBinary!"="(varLit, new JsBinary!"&&"(varLit,
				compare(indexArray(left, i), indexArray(right, i), arr.type, loop.states)));
			return varLit;
		} else if (auto str = cast(Struct) type) {
			if (str.types.length == 0) {
				return new JsLit("true");
			}
			if (str.types.length == 0) {
				return compare(indexStruct(left, 0), indexStruct(right, 0), str.types[0],
					depend);
			} else {
				auto ret = new JsBinary!"&&"();
				auto current = ret;
				foreach (c, t; str.types) {
					current.left = compare(indexStruct(left, c),
						indexStruct(right, c), type, depend);
					if (c == str.types.length - 2) {
						current.right = compare(indexStruct(left, c + 1),
							indexStruct(right, c + 1), type, depend);
						break;
					}
					auto next = new JsBinary!"&&"();
					current.right = next;
					current = next;
				}
				return ret;
			}
		} else {
			assert(0);
		}
	}

	JsExpr genTmp(JsExpr share, JsExpr init, ref JsState[] depend) {
		if (share) {
			if (init) {
				depend ~= new JsBinary!"="(share, init);
			}
		} else {
			auto name = genName();
			share = new JsLit(name);
			depend ~= new JsVarDef(name, init ? init : new JsLit("undefined"));
		}
		return share;
	}

	JsExpr returnWrap(JsExpr result, Usage self, Usage request, Type type, ref JsState[] depend) {
		if (request.share && self.share) {
			assert(request.share == self.share);
			return null;
		}
		if (request.cache == Eval.none) {
			if (self.cache == Eval.once) {
				depend ~= result;
			}
			return null;
		}
		if (request.cache == Eval.once) {
			assert(request.unique != Unique.same); //doesn't make sense
			if (request.unique == Unique.copy && self.unique != Unique.copy) {
				return onceCopy(result, type, depend);
			}
			return result;
		}
		assert(request.cache == Eval.any);
		if (self.cache != Eval.any) {
			auto ret = genTmp(null, result, depend);
			if (request.unique == Unique.copy) {
				return copy(ret, type);
			}
			return ret;
		}

		if (request.unique == Unique.copy && self.unique != Unique.copy) {
			return copy(result, type);
		}
		if (request.unique == Unique.same && self.unique != Unique.same) {
			auto ret = genTmp(null, result, depend);
			return ret;
		}
		assert(request.unique == self.unique);
		return result;
	}

	struct Wrap {
		Usage request;
		Type type;
		JsState[]* depend;
	}

	JsExpr returnWrap(JsExpr result, Usage self, Wrap wrap) {
		return returnWrap(result, self, wrap.request, wrap.type, *wrap.depend);
	}

	void ignoreShare(ref Usage usage) {
		usage.share = null;
	}

	JsExpr genVal(Value value, Trace trace, Usage usage, ref JsState[] depend) {
		auto args = Wrap(usage, value.type, &depend);
		if (auto lit = cast(IntLit) value) {
			return returnWrap(new JsLit(intLitToString(lit)), Usage.literal, args);
		} else if (auto lit = cast(BoolLit) value) {
			if (lit.yes) {
				return returnWrap(new JsLit("true"), Usage.literal, args);
			} else {
				return returnWrap(new JsLit("false"), Usage.literal, args);
			}
		} else if (auto lit = cast(CharLit) value) {
			return returnWrap(new JsLit('"' ~ escape(lit.value) ~ '"'), Usage.literal,
				args);
		} else if (auto lit = cast(StructLit) value) {
			ignoreShare(usage);
			auto fields = lit.values;
			JsExpr[] exprs;
			exprs.length = fields.length;
			foreach (i, field; fields) {
				exprs[i] = genVal(field, trace, Usage.container(usage), depend);
			}
			return returnWrap(new JsArray(exprs), Usage.container(usage), args);
		} else if (auto var = cast(Variable) value) {
			Trace subtrace;
			auto src = trace.var(var.name, var.namespace, subtrace);
			assert(src);
			JsExpr outvar;
			if (cast(ModuleVar) src) {
				auto modTrace = cast(Module.ModuleTrace) subtrace;
				auto names = modTrace.m.namespace.chain(only(var.name));
				foreach (c, name; names.enumerate) {
					if (c == 0) {
						outvar = new JsLit(name);
					} else {
						outvar = new JsDot(outvar, name);
					}
				}
			} else {
				assert(var.namespace is null);
				outvar = new JsLit(var.name);
			}
			if (src.heap) {
				outvar = new JsIndex(outvar, new JsLit("0"));
			}
			return returnWrap(outvar, Usage.variable, args);
		} else if (auto iF = cast(If) value) {
			auto state = new JsIf();
			state.cond = genVal(iF.cond, trace, Usage.once, depend);
			if (usage.cache == Eval.none) {
				auto yes = genVal(iF.yes, trace, Usage.none, state.yes);
				auto no = genVal(iF.no, trace, Usage.none, state.no);
				depend ~= state;
				return null;
			}

			auto tmp = genTmp(usage.share, null, depend);

			auto yes = genVal(iF.yes, trace, Usage.shareUsage(tmp), state.yes);
			auto no = genVal(iF.no, trace, Usage.shareUsage(tmp), state.no);

			if (yes) {
				state.yes ~= new JsBinary!"="(tmp, yes);
			}
			if (no) {
				state.no ~= new JsBinary!"="(tmp, no);
			}
			depend ~= state;
			return returnWrap(tmp, Usage.variable, args);
		} else if (auto wh = cast(While) value) {
			JsState[] condStates;
			auto cond = genVal(wh.cond, trace, Usage.once, condStates);
			auto state = new JsWhile();
			if (condStates.length == 0) {
				state.cond = cond;
				genVal(wh.state, trace, Usage.none, state.states);
			} else {
				state.cond = new JsLit("true");
				state.states ~= condStates;
				state.states ~= new JsIf(new JsPrefix!"!"(cond), [new JsBreak()], []);
				genVal(wh.state, trace, Usage.none, state.states);
			}
			depend ~= state;
			return returnWrap(new JsArray([]), Usage.literal, args);
		} else if (auto ne = cast(New) value) {
			auto ptr = new JsArray([genVal(ne.value, trace, Usage.container(usage),
				depend)]);
			return returnWrap(ptr, Usage.container(usage), args);
		} else if (auto na = cast(NewArray) value) {
			auto len = genVal(na.length, trace, Usage.copy, depend);
			auto val = genVal(na.value, trace, Usage.copy, depend);
			auto lit = genTmp(usage.share, new JsArray(), depend);
			auto loopInc = genName();
			auto incLit = new JsLit(loopInc);
			depend ~= new JsFor(new JsVarDef(loopInc, new JsLit("0")),
				new JsBinary!"<"(incLit, len), new JsPostfix!"++"(incLit),
				[new JsBinary!"="(new JsIndex(lit, incLit), val)]);
			return returnWrap(lit, Usage.variable, args);
		} else if (auto ca = cast(Cast) value) {
			ignoreShare(usage);
			auto val = genVal(ca.value, trace, usage, depend);
			if (sameType(ca.value.type, ca.wanted)) {
				return returnWrap(val, usage, args);
			} else if (sameType(ca.value.type, new Struct())) {
				return returnWrap(defaultValue(ca.wanted), Usage.literal, args);
			} else if (cast(UInt) ca.wanted.actual || cast(Int) ca.wanted.actual) {
				return returnWrap(castInt(val, ca.wanted), usage, args);
			}
			assert(0);
		} else if (auto dot = cast(Dot) value) {
			ignoreShare(usage);
			auto val = genVal(dot.value, trace, usage, depend);
			JsExpr result;
			if (dot.index.peek!string) {
				if (cast(Array) dot.value.type.actual) {
					return returnWrap(new JsDot(val, "length"), usage, args);
				}
				auto stru = cast(Struct)(dot.value.type.actual);
				result = indexStruct(val, stru.names[dot.index.get!string]);
			} else {
				result = indexStruct(val, dot.index.get!BigInt.to!size_t);
			}
			return returnWrap(result, usage, args);
		} else if (auto arr = cast(ArrayIndex) value) {
			ignoreShare(usage);
			auto array = genVal(arr.array, trace, Usage.copy, depend);
			auto index = genVal(arr.index, trace, usage, depend);
			auto result = indexArray(array, index);
			return returnWrap(result, Usage.container(usage), args);
		} else if (auto func = cast(FCall) value) {
			auto funcPtr = genVal(func.fptr, trace, Usage.once, depend);
			auto arg = genVal(func.arg, trace, Usage.copy, depend);
			auto expr = new JsCall(funcPtr, [arg]);
			return returnWrap(expr, Usage.once, args);
		} else if (auto slice = cast(Slice) value) {
			auto array = genVal(slice.array, trace, Usage.copy, depend);
			auto left = genVal(slice.left, trace, Usage.copy, depend);
			auto right = genVal(slice.right, trace, Usage.copy, depend);
			auto expr = new JsObject([Tuple!(string, JsExpr)("data",
				internalArray(array)), Tuple!(string, JsExpr)("start",
				new JsBinary!"+"(arrayStart(array), left)), Tuple!(string,
				JsExpr)("length", new JsBinary!"-"(right, left))]);
			return returnWrap(expr, Usage.literal, args);
		} else if (auto str = cast(StringLit) value) {
			string result;
			foreach (c; str.str) {
				result ~= escape(c);
			}
			auto expr = new JsCall(new JsDot(new JsLit("libtypi"),
				"jsStringToTypiString"), [new JsLit('"' ~ result ~ '"')]);
			return returnWrap(expr, Usage.literal, args);
		} else if (auto arr = cast(ArrayLit) value) {
			auto ret = new JsArray();
			foreach (val; arr.values) {
				ret.exprs ~= genVal(val, trace, Usage.copy, depend);
			}
			return returnWrap(ret, Usage.literal, args);
		} else if (auto bin = cast(Binary!"==") value) {
			auto left = genVal(bin.left, trace, Usage.copy, depend);
			auto right = genVal(bin.right, trace, Usage.copy, depend);
			auto expr = compare(left, right, bin.left.type, depend);
			return returnWrap(expr, Usage.literal, args);
		} else if (auto bin = cast(Binary!"!=") value) {
			auto left = genVal(bin.left, trace, Usage.copy, depend);
			auto right = genVal(bin.right, trace, Usage.copy, depend);
			auto expr = new JsPrefix!"!"(compare(left, right, bin.left.type, depend));
			return returnWrap(expr, Usage.literal, args);
		} else if (auto bin = cast(Binary!"=") value) {
			return genValAssign(bin.left, bin.right, trace, usage, depend);
		} else if (auto bin = cast(Binary!"~") value) {
			auto left = genVal(bin.left, trace, Usage.copy, depend);
			auto right = genVal(bin.right, trace, Usage.copy, depend);
			auto lit = genTmp(usage.share, new JsArray(), depend);
			auto i = new JsLit(genName());
			auto loop = new JsFor(new JsVarDef(i.value, new JsLit("0")),
				new JsBinary!"<"(i, arrayLength(left)), new JsPostfix!"++"(i), []);
			depend ~= loop;
			loop.states ~= new JsBinary!"="(new JsIndex(lit, i),
				copy(indexArray(left, i), (cast(Array) bin.left.type.actual).type));
			auto loop2 = new JsFor(new JsVarDef(i.value, arrayLength(left)),
				new JsBinary!"<"(i, new JsBinary!"+"(arrayLength(left), arrayLength(right))),
				new JsPostfix!"++"(i), []);
			depend ~= loop;
			loop2.states ~= new JsBinary!"="(new JsIndex(lit, i),
				copy(indexArray(right, new JsBinary!"-"(i, arrayLength(left))),
				(cast(Array) bin.left.type.actual).type));
			return returnWrap(lit, Usage.variable, args);
		} else if (auto pre = cast(Prefix!"*") value) {
			ignoreShare(usage);
			auto val = genVal(pre.value, trace, usage, depend);
			return returnWrap(indexPointer(val), usage, args);
		} else if (auto pre = cast(Prefix!"&") value) {
			auto sub = pre.value;
			if (auto var = cast(Variable) sub) {
				Trace subtrace;
				auto src = trace.var(var.name, var.namespace, subtrace);
				assert(src);
				JsExpr outvar;
				if (cast(ModuleVar) src) {
					auto names = var.namespace.chain(only(var.name));
					foreach (c, name; names.enumerate) {
						if (c == 0) {
							outvar = new JsLit(name);
						} else {
							outvar = new JsDot(outvar, name);
						}
					}
				} else {
					assert(var.namespace is null);
					outvar = new JsLit(var.name);
				}
				return returnWrap(outvar, Usage.literal, args);
			} else if (auto dot = cast(Dot) sub) {
				ignoreShare(usage);
				auto stru = dot.value;
				auto structType = cast(Struct) stru.type.actual;
				assert(structType);
				//todo bug, can't get address of .length
				auto structValue = genVal(stru, trace, usage, depend);
				size_t index;
				if (dot.index.peek!string) {
					index = structType.names[dot.index.get!string];
				} else {
					index = dot.index.get!BigInt.to!size_t;
				}
				auto expr = new JsObject([Tuple!(string, JsExpr)("data",
					structValue), Tuple!(string, JsExpr)("start", new JsLit(index.to!string))]);
				return returnWrap(expr, Usage.container(usage), args);
			}
			if (auto arrIndex = cast(ArrayIndex) sub) {
				ignoreShare(usage);
				auto arr = genVal(arrIndex.array, trace, Usage.copy, depend);
				auto index = genVal(arrIndex.index, trace, usage, depend);
				auto expr = new JsObject([Tuple!(string, JsExpr)("data",
					internalArray(arr)), Tuple!(string, JsExpr)("start",
					new JsBinary!"+"(arrayStart(arr), index))]);
				return returnWrap(expr, Usage.container(usage), args);
			}
			if (auto def = cast(Prefix!"*") sub) {
				return genVal(def.value, trace, usage, depend);
			}
			assert(0);
		} else if (auto sc = cast(Scope) value) {
			auto subt = sc.genTrace(trace);
			scopeStack ~= Tuple!(JsLabel, string)(null, "");
			JsState[] states;
			foreach (state; sc.states) {
				if (auto val = state.peek!Value) {
					genVal(*val, subt, Usage.none, states);
				} else {
					auto var = state.get!ScopeVar;
					auto val = genVal(var.def, subt, Usage(Unique.copy, Eval.once),
						states);
					if (var.heap) {
						states ~= new JsVarDef(var.name, new JsArray([val]));
					} else {
						states ~= new JsVarDef(var.name, val);
					}
					(cast(Scope.ScopeTrace)(subt)).vars[var.name] = var;
				}
			}
			if (scopeStack[$ - 1][1] != "") {
				auto jsScope = cast(JsScope) scopeStack[$ - 1][0];
				auto var = scopeStack[$ - 1][1];
				depend ~= new JsVarDef(var, defaultValue(sc.type));
				jsScope.states ~= states;
				depend ~= jsScope;
				scopeStack.popBack;
				return returnWrap(new JsLit(var), Usage.variable, args);
			} else {
				scopeStack.popBack;
				depend ~= states;
				return returnWrap(new JsArray(), Usage.literal, args);
			}
		} else if (auto funcLit = cast(FuncLit) value) {
			auto subt = funcLit.genTrace(trace);
			auto result = new JsFuncLit([funcLit.fvar.name], []);
			auto val = genVal(funcLit.text, subt, Usage(Unique.copy, Eval.once), result.states);
			if (!returns(result.states)) {
				result.states ~= new JsReturn(val);
			}
			return returnWrap(result, Usage.literal, args);
		} else if (auto ret = cast(Return) value) {
			auto val = genVal(ret.value, trace, Usage(Unique.copy, Eval.once), depend);
			size_t stop;
			if (ret.upper == uint.max) {
				stop = 0;
			} else {
				stop = scopeStack.length - 1 - ret.upper;
			}
			if (stop == 0) {
				depend ~= new JsReturn(val);
			} else {
				if (scopeStack[stop][0] is null) {
					scopeStack[stop][0] = new JsScope;
				}
				if (scopeStack[stop][0].label == "") {
					scopeStack[stop][0].label = genName();
				}
				if (scopeStack[stop][1] == "") {
					scopeStack[stop][1] = genName();
				}
				auto label = scopeStack[stop][0].label;
				auto var = scopeStack[stop][1];
				depend ~= new JsBinary!"="(new JsLit(var), val);
				depend ~= new JsBreak(label);
			}
			return returnWrap(new JsArray(), Usage.literal, args);
		} else if (auto ext = cast(ExternJS) value) {
			return returnWrap(new JsLit(ext.external), Usage.literal, args);
		} else {
			foreach (o; staticForeach!("*", "/", "%", "+", "-", "|", "^", "<<", ">>",
					">>>")) {
				if (auto bin = cast(Binary!o) value) {
					ignoreShare(usage);
					auto left = genVal(bin.left, trace, usage, depend);
					auto right = genVal(bin.right, trace, usage, depend);
					return returnWrap(castInt(new JsBinary!o(left, right), bin.type),
						usage, args);
				}
			}
			foreach (o; staticForeach!("<=", ">=", "<", ">", "&&", "||")) {
				if (auto bin = cast(Binary!o) value) {
					ignoreShare(usage);
					auto left = genVal(bin.left, trace, usage, depend);
					auto right = genVal(bin.right, trace, usage, depend);
					return returnWrap(new JsBinary!o(left, right), usage, args);
				}
			}

			foreach (o; staticForeach!("-", "~", "!")) {
				if (auto pre = cast(Prefix!o) value) {
					ignoreShare(usage);
					return returnWrap(new JsPrefix!"!"(genVal(pre.value, trace,
						usage, depend)), usage, args);
				}
			}
			assert(0);
		}
	}

	JsExpr genValAssign(Value value, Value rightValue, Trace trace, Usage usage, ref JsState[] depend) {
		JsExpr outvar;
		ignoreShare(usage);
		auto right = genVal(rightValue, trace, Usage.copy, depend);
		if (auto var = cast(Variable) value) {
			Trace subtrace;
			auto src = trace.var(var.name, var.namespace, subtrace);
			assert(src);
			if (cast(ModuleVar) src) {
				auto names = var.namespace.chain(only(var.name));
				foreach (c, name; names.enumerate) {
					if (c == 0) {
						outvar = new JsLit(name);
					} else {
						outvar = new JsDot(outvar, name);
					}
				}
			} else {
				assert(var.namespace is null);
				outvar = new JsLit(var.name);
			}
			if (src.heap) {
				outvar = new JsIndex(outvar, new JsLit("0"));
			}
			outvar = new JsBinary!"="(outvar, right);
		} else {
			auto sub = genVal(value, trace, Usage.once, depend);
			outvar = new JsBinary!"="(sub, right);
		}
		return returnWrap(outvar, Usage(Unique.no, Eval.once), usage, value.type, depend);
	}
}

string escape(dchar d) {
	if (d == '\0') {
		return "\\0"; //"\0" in js
	} else if (d == '\'') {
		return "'";
	} else if (d == '"') {
		return "\\" ""; //"\"" in js
	}
	return d.to!string;
}

unittest {
	import std.stdio;
	import semantic;

	auto l = Loader(["test/codegen"]);
	Module[string[]] all;
	Module[string[]] wanted;
	readFiles(l, [["main"]], wanted, all);
	processModules(all.values);
	auto val = genJS(all.values);
	writeln(val);
}
