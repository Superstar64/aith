/+
	Copyright (C) 2015-2017  Freddy Angel Cubas "Superstar64"
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
module semantic.semantic;
import std.algorithm;
import std.array;
import std.bigint;
import std.conv;
import std.file;
import std.meta;
import std.range;
import std.typecons;

static import Parser = parser.ast;
import semantic.ast;
import misc;

struct Equivalence {
	PolymorphicType left;
	PolymorphicType right;
	Position position;
	int line;
	this(PolymorphicType left, PolymorphicType right, Position position, int line = __LINE__) {
		this.left = left;
		this.right = right;
		this.position = position;
		this.line = line;
		assert(left);
		assert(right);
	}
}

class Context {
	this(Module global, PolymorphicVariable argumentType, string symbolName,
			Tuple!()[Parser.Expression] recursionCheck) {
		this.global = global;
		this.argumentType = argumentType;
		this.symbolName = symbolName;
		this.recursionCheck = recursionCheck;
	}

	Module global;
	bool explicitInfer;
	PolymorphicVariable argumentType;
	string symbolName;
	Tuple!()[Parser.Expression] recursionCheck;
	Equivalence[] typeChecks;
	Tuple!(PolymorphicType, Position)[] types;
	ScopeVarImpl!false[] vars;
	void delegate() @system[] futures;

	Expression search(string name) {
		foreach (var; vars.retro) {
			if (var.name == name) {
				return var;
			}
		}
		if (name in global.aliases) {
			return global.aliases[name].element;
		} else if (name in global.rawSymbols) {
			processModuleSymbol(global, global.rawSymbols[name], recursionCheck);
			return global.aliases[name].element;
		}
		return null;
	}

	auto store() {
		static struct Storage {
			ScopeVarImpl!false[] vars;
			Context that;
			auto restore() {
				that.vars = vars;
				return that;
			}
		}

		return Storage(vars, this);
	}
}

Module lazyCreateModule(Parser.Module parser) {
	auto mod = new Module();
	foreach (symbol; parser.symbols) {
		check(!(symbol.name in mod.rawSymbols), "Symbol already exists", symbol.position);
		mod.rawSymbols[symbol.name] = symbol;
	}
	return mod;
}

void processModule(Module mod) {
	foreach (symbol; mod.rawSymbols) {
		if (symbol.name in mod.aliases) {
			continue;
		}
		processModuleSymbol(mod, symbol, null);
	}
}

void dispatchFutures(Context context) {
	while (!context.futures.empty) {
		context.futures.front()();
		context.futures.popFront;
	}
}

PolymorphicType[PolymorphicVariable] mapSubstitions(Context context, Subsitution[] pending) {
	PolymorphicType[][PolymorphicVariable] map;
	foreach (substition; pending) {
		map[substition.from] ~= substition.to;
	}
	loop: while (true) {
		foreach (key; map.byKey) {
			if (map[key].length > 1) {
				auto substitions = mapSubstitions(context,
						typeMatch(map[key][0], map[key][1], Position.init));
				foreach (ref value; map.byValue) {
					value = value.map!(a => a.specialize(substitions, new TypeTransition())).array;
				}
				map[key].popFront;
				foreach (substition; substitions.byKey) {
					map[substition] ~= substitions[substition];
				}
				continue loop;
			}
		}
		break;
	}
	PolymorphicType[PolymorphicVariable] solution;
	foreach (key; map.byKey) {
		assert(map[key].length == 1);
		solution[key] = map[key][0];
	}
	//todo is this necessary
	foreach (ref value; solution.byValue) {
		value = value.specialize(solution, new TypeTransition());
	}
	return solution;
}

void processModuleSymbol(Module mod, Parser.ModuleVarDef symbol,
		Tuple!()[Parser.Expression] recursionCheck) {
	auto context = new Context(mod, null, symbol.name, recursionCheck);
	Wrapper!Expression value;
	if (symbol.explicitType) {
		context.explicitInfer = true;
		value = semanticMain(symbol.value, context);
		mod.aliases[symbol.name] = ModuleAlias(value, symbol.visible);
		dispatchFutures(context);
		auto explicitType = semanticMain(symbol.explicitType, context).assumeType;
		context.typeChecks ~= Equivalence(value.assumePolymorphic.type,
				explicitType, symbol.position);
	} else {
		value = semanticMain(symbol.value, context);
		mod.aliases[symbol.name] = ModuleAlias(value, symbol.visible);
		dispatchFutures(context);
	}

	if (auto result = value.castTo!PolymorphicExpression) {
		auto pending = context.typeChecks.map!(check => typeMatch(check.left,
				check.right, check.position)).joiner.array;
		PolymorphicType[PolymorphicVariable] substitions = mapSubstitions(context, pending);
		auto expected = result.type.specialize(substitions, new TypeTransition()).parameters;
		foreach (type; context.types) {
			check(isSubSet(type[0].specialize(substitions, new TypeTransition())
					.parameters, expected), "unable to infer type", type[1]);
		}
		result = result.specialize(substitions, new Transition(context.global));
		value = value.mapWrap!(a => result);
	}
	if (!symbol.manifest) {
		auto runtime = value.assumeRuntime;
		auto definition = new ModuleVarDef(runtime, symbol.visible, symbol.name);
		mod.exports[definition.name] = definition;
		auto wrappedDefinition = wrapper(definition, symbol.position);
		value = wrapper!Expression(new ModuleVarRef(wrappedDefinition), symbol.position);
	}
	//reassign is intentional
	mod.aliases[symbol.name] = ModuleAlias(value, symbol.visible);
}

bool isInt(Type type) {
	return !!type.castTo!TypeInt;
}

//todo fix me reimplement using tryInfer with wanted = metaclass
Wrapper!Type assumeType(Wrapper!Expression value, string file = __FILE__, int line = __LINE__) {
	check(value.castTo!Type, "Expected type", value.position, file, line);
	return value.mapWrap!(a => a.castTo!Type);
}

Wrapper!RuntimeExpression assumeRuntime(E)(Wrapper!E value, string file = __FILE__,
		int line = __LINE__) {
	auto result = value.mapWrap!(castTo!RuntimeExpression);
	check(result, "Expected runtime value", value.position, file, line);

	return result;
}

Wrapper!PolymorphicExpression assumePolymorphic(Wrapper!Expression value,
		string file = __FILE__, int line = __LINE__) {
	auto result = value.mapWrap!(castTo!PolymorphicExpression);
	check(result, "Expected polymorphic value", value.position, file, line);

	return result;
}

Wrapper!Type semanticType(Parser.Expression that, Context context) {
	return assumeType(semanticMain(that, context));
}

auto semanticMain(Parser.Expression that, Context context) {
	if (that in context.recursionCheck) {
		error("Illegal Recursion", that.position);
	}
	context.recursionCheck[that] = Tuple!()();
	auto result = semanticImplDispatch(that, context);
	if (auto expr = result.castTo!PolymorphicExpression) {
		context.types ~= tuple(expr.type, that.position);
	}
	return Wrapper!(typeof(result))(result, that.position);
}

Expression semanticImplDispatch(Parser.Expression that, Context context) {
	return dispatch!(semanticImpl, Parser.Variable, Parser.TypeTuple, Parser.Index,
			Parser.Call, Parser.Dot, Parser.TypeBool, Parser.TypeChar,
			Parser.TypeInt, Parser.Import, Parser.IntLit, Parser.CharLit,
			Parser.BoolLit, Parser.TupleLit, Parser.FuncArgument, Parser.If,
			Parser.While, Parser.New, Parser.NewArray, Parser.Cast,
			Parser.Infer, Parser.Slice, Parser.Scope, Parser.FuncLit,
			Parser.StringLit, Parser.ArrayLit, Parser.ExternJs, Parser.Binary!"*",
			Parser.Binary!"/", Parser.Binary!"%", Parser.Binary!"+",
			Parser.Binary!"-", Parser.Binary!"~", Parser.Binary!"==",
			Parser.Binary!"!=", Parser.Binary!"<=", Parser.Binary!">=",
			Parser.Binary!"<", Parser.Binary!">", Parser.Binary!"&&",
			Parser.Binary!"||", Parser.Prefix!"-", Parser.Prefix!"*",
			Parser.Prefix!"&", Parser.Prefix!"!", Parser.Postfix!"(*)",
			Parser.Postfix!"[*]", Parser.Binary!"->", Parser.UseSymbol, Parser.TupleIndex)(that,
			context);
}

Expression semanticImpl(Parser.Variable that, Context context) {
	auto variable = context.search(that.name);
	check(!(variable is null), "Undefined variable", that.position);
	//todo check for closrure variable
	return variable;
}

auto typeStructFromTuple(Wrapper!Expression value) {
	if (auto tuple = value.castTo!(TupleLitCommon)) {
		auto types = tuple.values
			.map!assumeType
			.map!(a => a.convert!Type)
			.array;
		return value.mapWrap!(a => new TypeStruct(types).convert!Type);
	}
	return value.mapWrap!(a => null.convert!Type);
}

Expression semanticImpl(Parser.TypeTuple that, Context context) {
	return semanticMain(that.value, context).typeStructFromTuple;
}

Expression semanticImpl(Parser.UseSymbol that, Context context) {
	auto value = semanticMain(that.value, context);
	check(value.type.castTo!TypeImport, "scope resolution expect a module", that.position);
	auto mod = value.castTo!Import.mod;
	check(that.index in mod.aliases, "unknown module symbol", that.position);
	check(mod.aliases[that.index].visible, that.index ~ "is not visible", that.position);
	return mod.aliases[that.index].element;
}

Expression semanticImpl(Parser.Dot that, Context context) {
	auto value = semanticMain(that.value, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(value.type,
			new TypeArrayImpl!false(new NormalPolymorphicVariable), that.position);
	check(that.index == "length", "Arrays only have .length", that.position);
	return createLength(value);
}

Expression semanticImpl(Parser.Import that, Context context) {
	return new Import(that.mod);
}

Expression semanticImpl(Parser.TypeBool that, Context context) {
	return new TypeBool();
}

Expression semanticImpl(Parser.TypeChar that, Context context) {
	return new TypeChar();
}

void checkIntSize(int size, Position position) {
	check(size == 0 || size == 8 || size == 16 || size == 32, "Bad TypeInt Size", position);
}

Expression semanticImpl(Parser.TypeInt that, Context context) {
	checkIntSize(that.size, that.position);
	return new TypeInt(that.size, that.signed);
}

Expression semanticImpl(Parser.Postfix!"(*)" that, Context context) {
	auto value = semanticType(that.value, context);
	return new TypePointer(value);
}

Expression semanticImpl(Parser.Postfix!"[*]" that, Context context) {
	auto value = semanticType(that.value, context);
	return new TypeArray(value);
}

Expression semanticImpl(Parser.IntLit that, Context context) {
	return new IntLitImpl!false(new NumberPolymorphicVariable, that.value);
}

Expression semanticImpl(Parser.CharLit that, Context context) {
	return new CharLit(that.value);
}

Expression semanticImpl(Parser.BoolLit that, Context context) {
	return new BoolLit(that.yes);
}

Expression semanticImpl(Parser.TupleLit that, Context context) {
	auto values = that.values.map!(a => semanticMain(a, context)).array;
	return createTupleLit(values);
}

Expression semanticImpl(Parser.If that, Context context) {
	auto cond = semanticMain(that.cond, context).assumePolymorphic;
	auto yes = semanticMain(that.yes, context).assumePolymorphic;
	auto no = semanticMain(that.no, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(cond.type, new TypeBool, cond.position);
	context.typeChecks ~= Equivalence(yes.type, no.type, that.position);
	return createIf(cond, yes, no);
}

Expression semanticImpl(Parser.While that, Context context) {
	auto cond = semanticMain(that.cond, context).assumePolymorphic;
	auto state = semanticMain(that.state, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(cond.type, new TypeBool, cond.position);
	return createWhile(cond, state);
}

Expression semanticImpl(Parser.New that, Context context) {
	auto value = semanticMain(that.value, context).assumePolymorphic;
	return createNew(value);
}

Expression semanticImpl(Parser.NewArray that, Context context) {
	auto length0 = semanticMain(that.length, context).assumePolymorphic;
	auto value = semanticMain(that.value, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(length0.type, new TypeInt(0, false), length0.position);
	return createNewArray(length0, value);
}

Expression semanticImpl(Parser.Cast that, Context context) {
	auto argumentType = semanticType(that.type, context);
	return new CastPartial(argumentType);
}

Expression semanticImpl(Parser.Infer that, Context context) {
	auto argumentType = semanticType(that.type, context);
	return new InferPartial(argumentType);
}

//todo reimplement indexing tuples
Expression semanticImpl(Parser.Index that, Context context) {
	auto array = semanticMain(that.array, context).assumePolymorphic;
	auto index = semanticMain(that.index, context).assumePolymorphic;
	auto var = new NormalPolymorphicVariable;
	context.typeChecks ~= Equivalence(array.type, new TypeArrayImpl!false(var), array.position);
	context.typeChecks ~= Equivalence(index.type, new TypeInt(0, false), index.position);
	return createIndex(var, array, index);
}

Expression semanticImpl(Parser.TupleIndex that, Context context) {
	auto tuple = semanticMain(that.tuple, context).assumePolymorphic;
	auto index = that.index;
	PolymorphicVariable[] types = new NormalPolymorphicVariable[index + 1];
	foreach (ref type; types) {
		type = new NormalPolymorphicVariable();
	}
	auto type = new TuplePolymorphicVariable(types.map!(a => a.convert!PolymorphicType).array);
	context.typeChecks ~= Equivalence(tuple.type, type, that.position);
	return createTupleIndex(types[index], tuple, index);
}

Expression semanticImpl(Parser.Call that, Context context) {
	auto calle = semanticMain(that.calle, context);
	auto argument = semanticMain(that.argument, context);
	return dispatch!(semanticCall, TypeCastPartial, TypeInferPartial,
			PolymorphicType, CompileTimeType)(calle.type, calle, argument, that.position, context);
}

Expression semanticCall(TypeCastPartial type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position, Context context) {
	auto wanted = calle.castTo!CastPartial.value;
	check(argument.assumeRuntime.type.isInt && isInt(wanted), "Unknown cast request", position);
	return new CastInteger(argument.mapWrap!(castTo!RuntimeExpression), wanted);
}

Expression semanticCall(TypeInferPartial type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position, Context context) {
	auto argument1 = argument.assumePolymorphic;
	context.typeChecks ~= Equivalence(argument1.type, calle.castTo!InferPartial.value, position);
	return argument1;
}

Expression semanticCall(PolymorphicType type, Wrapper!Expression calle0,
		Wrapper!Expression argument0, Position position, Context context) {
	auto var = new NormalPolymorphicVariable;
	auto calle1 = calle0.assumePolymorphic;
	auto argument1 = argument0.assumePolymorphic;
	context.typeChecks ~= Equivalence(type, new TypeFunctionImpl!false(var,
			argument1.type), position);
	return createCall(var, calle1, argument1);
}

Expression semanticCall(CompileTimeType type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position, Context) {
	error("Unable to call", position);
	assert(0);
}

Expression semanticImpl(Parser.Slice that, Context context) {
	auto array = semanticMain(that.array, context).assumePolymorphic;
	auto left = semanticMain(that.left, context).assumePolymorphic;
	auto right = semanticMain(that.right, context).assumePolymorphic;

	auto type = new TypeArrayImpl!false(new NormalPolymorphicVariable);
	context.typeChecks ~= Equivalence(array.type, type, that.position);
	context.typeChecks ~= Equivalence(left.type, new TypeInt(0, false), that.position);
	context.typeChecks ~= Equivalence(right.type, new TypeInt(0, false), that.position);
	return createSlice(array, left, right);
}

Expression semanticImpl(Parser.Binary!"->" that, Context context) {
	auto left = semanticMain(that.left, context).assumeType;
	auto right = semanticMain(that.right, context).assumeType;
	return new TypeFunction(right, left);
}

//todo remove me
//wierd compiler bug

alias ParserBinary = Parser.Binary;
alias ParserPrefix = Parser.Prefix;

Expression semanticImpl(string op)(ParserBinary!op that, Context context)
		if (["<=", ">=", ">", "<"].canFind(op)) {
	auto left = semanticMain(that.left, context).assumePolymorphic;
	auto right = semanticMain(that.right, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(left.type, right.type, that.position);
	return createBinary!op(left, right);
}

Expression semanticImpl(string op)(ParserBinary!op that, Context context)
		if (["*", "/", "%", "+", "-"].canFind(op)) {
	auto left = semanticMain(that.left, context).assumePolymorphic;
	auto right = semanticMain(that.right, context).assumePolymorphic;
	auto type = new NumberPolymorphicVariable();
	context.typeChecks ~= Equivalence(left.type, type, that.position);
	context.typeChecks ~= Equivalence(right.type, type, that.position);
	return createBinary!op(left, right);
}

Expression semanticImpl(string op)(ParserBinary!op that, Context context)
		if (["==", "!="].canFind(op)) {
	auto left = semanticMain(that.left, context).assumePolymorphic;
	auto right = semanticMain(that.right, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(left.type, right.type, that.position);
	return createBinary!op(left, right);
}

Expression semanticImpl(string op)(ParserBinary!op that, Context context)
		if (["&&", "||"].canFind(op)) {
	auto left = semanticMain(that.left, context).assumePolymorphic;
	auto right = semanticMain(that.right, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(left.type, new TypeBool, that.position);
	context.typeChecks ~= Equivalence(right.type, new TypeBool, that.position);
	return createBinary!op(left, right);
}

Expression semanticImpl(string op)(ParserBinary!op that, Context context)
		if (op == "~") {
	auto left = semanticMain(that.left, context).assumePolymorphic;
	auto right = semanticMain(that.right, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(left.type, createTypeArray(right.type), that.position);
	return createBinary!op(left, right);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context)
		if (op == "!") {
	auto value = semanticMain(that.value, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(value.type, new TypeBool, that.position);
	return createPrefix!op(value);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context)
		if (op == "&") {
	auto value = semanticMain(that.value, context).assumePolymorphic.mapWrap!(
			castTo!PolymorphicLValueExpression);
	//todo add lvalues to type inferance
	check(value, "& only works on lvalues", that.position);
	return createAddress(value);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context)
		if (op == "-") {
	auto value = semanticMain(that.value, context).assumePolymorphic;
	auto type = new NumberPolymorphicVariable;
	context.typeChecks ~= Equivalence(value.type, type, that.position);
	return createPrefix!op(value);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context)
		if (op == "*") {
	auto value = semanticMain(that.value, context).assumePolymorphic;
	auto var = new NormalPolymorphicVariable;
	context.typeChecks ~= Equivalence(value.type, new TypePointerImpl!false(var), that.position);
	return createDeref(var, value);
}

Expression semanticImpl(string op)(ParserPrefix!op that, Context context)
		if (["+", "/"].canFind(op)) {
	error(op ~ " not supported", that.position);
	return null;
}

Wrapper!PolymorphicExpression semanticScope(Parser.Statement[] tail,
		Parser.Expression last, Context context) {
	if (tail.length == 0) {
		return last ? semanticMain(last, context).assumePolymorphic
			: wrapper!PolymorphicExpression(new TupleLit(null), Position.init);
	} else {
		auto head = tail[0];
		auto node = dispatch!(semanticScopeImpl, Parser.Assign,
				Parser.ScopeVarDef, Parser.Expression)(head, tail[1 .. $], last, context);
		return wrapper(node, head.position);
	}
}

PolymorphicExpression semanticScopeImpl(Parser.Assign that,
		Parser.Statement[] tail, Parser.Expression last, Context context) {
	auto left = semanticMain(that.left, context).assumePolymorphic.mapWrap!(
			castTo!PolymorphicLValueExpression);
	auto right = semanticMain(that.right, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(left.type, right.type, that.position);
	check(left, "Not an lvalue", that.left.position);
	return createAssign(left, right, semanticScope(tail, last, context));
}

PolymorphicExpression semanticScopeImpl(Parser.ScopeVarDef that,
		Parser.Statement[] tail, Parser.Expression last, Context context) {
	auto value = semanticMain(that.value, context).assumePolymorphic;
	if (that.explicitType) {
		auto explicitType = semanticType(that.explicitType, context);
		context.typeChecks ~= Equivalence(value.type, explicitType, that.position);
	}
	check(!that.manifest, "Manifest locals not yet supported", that.position);

	auto variable = createScopeVar(that.name, value);
	context.vars ~= variable;
	auto lastSemantic = semanticScope(tail, last, context);
	context.vars.popBack;

	return createScopeVarDef(variable, lastSemantic);
}

PolymorphicExpression semanticScopeImpl(Parser.Expression that,
		Parser.Statement[] tail, Parser.Expression last, Context context) {
	auto stateful = semanticMain(that, context).assumePolymorphic;
	context.typeChecks ~= Equivalence(stateful.type, new TypeStruct(), stateful.position);
	return createScope(stateful, semanticScope(tail, last, context));
}

Expression semanticImpl(Parser.Scope that, Context context) {
	return semanticScope(that.states, that.last, context);
}

Expression semanticImpl(Parser.FuncLit that, Context context) {
	if (context.argumentType) {
		error("only top level lambda are supported for now", that.position);
	}
	auto argumentType = new NormalPolymorphicVariable;
	context.argumentType = argumentType;
	auto returnType = new NormalPolymorphicVariable;
	auto type = new TypeFunctionImpl!false(returnType, argumentType);
	auto result = new FunctionLiteralImpl!false(type, context.symbolName, context.explicitInfer);
	auto old = context.store;
	context.futures ~= {
		context = old.restore;
		result.text = semanticMain(that.text, context).assumePolymorphic;
		context.typeChecks ~= Equivalence(returnType, result.text.type, that.position);
	};
	return result;
}

Expression semanticImpl(Parser.FuncArgument that, Context context) {
	check(!(context.argumentType is null), "$@ without function", that.position);
	return createFuncArgument(context.argumentType);
}

Expression semanticImpl(Parser.StringLit that, Context context) {
	return new StringLit(that.value);
}

Expression semanticImpl(Parser.ArrayLit that, Context context) {
	auto var = new NormalPolymorphicVariable;
	auto type = new TypeArrayImpl!false(var);
	auto values = that.values.map!(a => semanticMain(a, context).assumePolymorphic).array;
	foreach (value; values) {
		context.typeChecks ~= Equivalence(var, value.type, that.position);
	}
	return createArrayLit(type, values);
}

Expression semanticImpl(Parser.ExternJs that, Context context) {
	return new ExternJsImpl!false(new NormalPolymorphicVariable, that.name);
}
