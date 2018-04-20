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
module semantic;
import std.algorithm;
import std.array;
import std.bigint;
import std.conv;
import std.file;
import std.meta;
import std.range;
import std.typecons;

static import Parser = parserast;
import semanticast;
import misc;

Module lazyCreateModule(Parser.Module parser) {
	auto mod = new Module();
	foreach (symbol; parser.symbols) {
		if (symbol.name in mod.rawSymbols) {
			error("Symbol already exists", symbol.position);
		}
		mod.rawSymbols[symbol.name] = symbol;
	}
	return mod;
}

void processModule(Module mod) {
	foreach (symbol; mod.rawSymbols) {
		if (symbol.name in mod.aliases) {
			continue;
		}
		processModuleSymbol(mod, symbol);
	}
}

void processModuleSymbol(Module mod, Parser.ModuleVarDef symbol) {
	auto context = Context(mod, null, null, [mod]);
	//todo refactor this
	Parser.FuncLit whenFunctionParser;
	FuncLit whenFunctionSemantic;
	mod.aliases[symbol.name] = semantic1(symbol, context, whenFunctionParser,
			whenFunctionSemantic);
	if (whenFunctionParser) {
		semantic1FuncFinish(whenFunctionParser, whenFunctionSemantic, context);
	}
}

Wrapper!Expression semantic1(Parser.ModuleVarDef that, Context context,
		out Parser.FuncLit whenFunctionParser, out FuncLit whenFunctionSemantic) {
	if (that.visible) {
		context.global.visible[that.name] = Tuple!()();
	}
	Wrapper!Expression value;
	if (auto func = that.value.castTo!(Parser.FuncLit)) {
		whenFunctionParser = func;
		value = semantic1Func(func, that.name, context, whenFunctionSemantic);
	} else if (auto ext = that.value.castTo!(Parser.ExternJs)) {
		value = semantic1Extern(ext, that.name, context);
	} else {
		value = semantic1(that.value, context);
	}
	if (!value.ispure) {
		error("Impure expression in global variable", value.position);
	}
	auto definition = new ModuleVarDef(value, that.visible, that.name);
	if (that.explicitType) {
		auto explicitType = semantic1Type(that.explicitType, context);
		value = implicitCast(value, explicitType);
	}
	if (that.manifest) {
		return Wrapper!Expression(value);
	}
	context.global.exports[definition.name] = definition;
	return Wrapper!Expression(new ModuleVarRef(Wrapper!ModuleVarDef(definition, that.position)));
}

Wrapper!Expression semantic1Func(Parser.FuncLit that, string name,
		Context context, out FuncLit result) {
	auto explicitReturn = that.explicitReturn ? semantic1Type(that.explicitReturn,
			context) : Wrapper!Type(null, Position());
	auto argument = semantic1Type(that.argument, context);
	result = new FuncLit(name, explicitReturn, argument);
	if (!explicitReturn) {
		context = Context(context.global, result, null, context.searchSpace);
		result.text = semantic1(that.text, context);
	}
	context.global.exports[name] = result;
	return Wrapper!Expression(result, that.position);
}

//explicitTypes functions have defered analysis
void semantic1FuncFinish(Parser.FuncLit that, FuncLit result, Context context) {
	context = Context(context.global, result, null, context.searchSpace);
	if (result.explicitReturn) {
		result.text = semantic1(that.text, context);
		result.text = implicitCast(result.text, result.explicitReturn);
	}
}

bool isInt(Type type) {
	return !!type.castTo!TypeUInt || !!type.castTo!TypeInt;
}

Wrapper!Expression tryCast(bool implicit)(Wrapper!Expression value,
		Wrapper!Type wanted, Position position) {
	if (sameType(value.type, wanted)) {
		return Wrapper!Expression(value, position);
	} else if ((implicit ? !!value.castTo!IntLit : isInt(value.type)) && isInt(wanted)) {
		return Wrapper!Expression(new CastInteger(value, wanted), position);
	} else if (auto ext = value.castTo!ExternJs) {
		return Wrapper!Expression(new CastExtern(Wrapper!ExternJs(ext,
				value.position), wanted), position);
	} else {
		return Wrapper!Expression(null);
	}
}

Wrapper!Expression explicitCast(Wrapper!Expression value, Wrapper!Type wanted, Position position) {
	auto result = tryCast!false(value, wanted, position);
	if (!result) {
		error("Unknown cast request", position);
	}
	return result;
}

//todo fix me reimplement auto casting
Wrapper!Type assumeType(Wrapper!Expression value) {
	if (auto tuple = value.castTo!TupleLit) {
		return Wrapper!Type(new TypeStruct(tuple.values.map!assumeType.map!(a => a._value)
				.array), value.position);
	}
	if (!value.castTo!Type) {
		error("Expected type", value.position);
	}
	return Wrapper!Type(value.castTo!Type, value.position);
}

Wrapper!Expression implicitCast(Wrapper!Expression value, Type wanted) {
	auto result = tryCast!true(value, Wrapper!Type(wanted), value.position);
	if (!result) {
		error("Unknown cast request", value.position);
	}
	return result;
}

void implicitCastDual(ref Wrapper!Expression value1, ref Wrapper!Expression value2,
		Position position) {
	auto newValue1 = tryCast!true(value1, Wrapper!Type(value2.type), position);
	auto newValue2 = tryCast!true(value2, Wrapper!Type(value1.type), position);
	if (newValue1) {
		value1 = newValue1;
		return;
	}
	if (newValue2) {
		value2 = newValue2;
		return;
	}
	if (!sameType(value1.type, value2.type)) {
		error("Not same type", position);
	}
}

Wrapper!Type semantic1Type(Parser.Expression that, Context context) {
	return assumeType(semantic1(that, context));
}

auto semantic1(T)(T that, Context context) {
	auto result = semantic1Impl(that, context);
	return Wrapper!(typeof(result))(result, that.position);
}

Expression semantic1Impl(Parser.Expression that, Context context) {
	return dispatch!(semantic1Impl, Parser.Variable, Parser.TypeStruct, Parser.Index,
			Parser.Call, Parser.Dot, Parser.TypeBool, Parser.TypeChar,
			Parser.TypeInt, Parser.TypeUInt, Parser.Import, Parser.IntLit, Parser.CharLit,
			Parser.BoolLit, Parser.TupleLit, Parser.FuncArgument, Parser.If,
			Parser.While, Parser.New, Parser.NewArray, Parser.Cast, Parser.Slice,
			Parser.Scope, Parser.FuncLit, Parser.StringLit, Parser.ArrayLit,
			Parser.ExternJs, Parser.Binary!"*", Parser.Binary!"/",
			Parser.Binary!"%", Parser.Binary!"+", Parser.Binary!"-",
			Parser.Binary!"~", Parser.Binary!"==", Parser.Binary!"!=",
			Parser.Binary!"<=", Parser.Binary!">=", Parser.Binary!"<",
			Parser.Binary!">", Parser.Binary!"&&", Parser.Binary!"||",
			Parser.Prefix!"-", Parser.Prefix!"*", Parser.Prefix!"&",
			Parser.Prefix!"!", Parser.Postfix!"(*)")(that, context);
}

Expression semantic1Impl(Parser.Variable that, Context context) {
	auto variable = context.search(that.name);
	if (variable is null) {
		error("Unknown variable", that.position);
	}
	if (auto scopeVariable = variable.castTo!ScopeVarRef) {
		if (!(scopeVariable.definition in context.localVariables)) {
			error("Escaping variable", that.position);
		}
	}
	return variable;
}

Expression semantic1Impl(Parser.TypeStruct that, Context context) {
	return new StructFunc;
}

Expression semantic1Impl(Parser.Dot that, Context context) {
	auto value = semantic1(that.value, context);
	return dispatch!(semantic1Dot, TypeArray, TypeImport)(value.type, value,
			that.index, that.position, context);
}

Expression semantic1Dot(TypeArray type, Wrapper!Expression value, string index,
		Position position, Context context) {
	if (index != "length") {
		error("Arrays only have .length", position);
	}
	return new Length(value);
}

Expression semantic1Dot(TypeImport type, Wrapper!Expression value, string index,
		Position position, Context context) {
	auto mod = value.castTo!Import.mod;
	auto symbol = mod.search(index);
	if (!(index in mod.visible)) {
		error(index ~ "is not visible", position);
	}
	return symbol;
}

Expression semantic1Dot(Type type, Wrapper!Expression value, string index,
		Position position, Context context) {
	error("unable to dot", position);
	assert(0);
}

Expression semantic1Impl(Parser.Import that, Context context) {
	return new Import(that.mod);
}

Expression semantic1Impl(Parser.TypeBool that, Context context) {
	return new TypeBool();
}

Expression semantic1Impl(Parser.TypeChar that, Context context) {
	return new TypeChar();
}

void checkIntSize(int size, Position position) {
	if (size == 0) {
		return;
	}
	if (!recurrence!((a, n) => a[n - 1] / 2)(size).until(1).map!(a => a % 2 == 0).all) {
		error("Bad TypeInt Size", position);
	}
}

Expression semantic1Impl(Parser.TypeInt that, Context context) {
	checkIntSize(that.size, that.position);
	return new TypeInt(that.size);
}

Expression semantic1Impl(Parser.TypeUInt that, Context context) {
	checkIntSize(that.size, that.position);
	return new TypeUInt(that.size);
}

Expression semantic1Impl(Parser.Postfix!"(*)" that, Context context) {
	auto value = semantic1Type(that.value, context);
	return new TypePointer(value);
}

Expression semantic1Impl(Parser.IntLit that, Context context) {
	return new IntLit(that.value);
}

Expression semantic1Impl(Parser.CharLit that, Context context) {
	return new CharLit(that.value);
}

Expression semantic1Impl(Parser.BoolLit that, Context context) {
	return new BoolLit(that.yes);
}

Expression semantic1Impl(Parser.TupleLit that, Context context) {
	auto values = that.values.map!(a => semantic1(a, context)).array;
	return new TupleLit(values);
}

Expression semantic1Impl(Parser.FuncArgument that, Context context) {
	if (context.local is null) {
		error("$@ without function", that.position);
	}
	return new FuncArgument(context.local.argument);
}

Expression semantic1Impl(Parser.If that, Context context) {
	auto cond = semantic1(that.cond, context);
	auto yes = semantic1(that.yes, context);
	auto no = semantic1(that.no, context);
	cond = implicitCast(cond, new TypeBool);
	implicitCastDual(yes, no, that.position);
	return new If(cond, yes, no);
}

Expression semantic1Impl(Parser.While that, Context context) {
	auto cond = semantic1(that.cond, context);
	auto state = semantic1(that.state, context);
	cond = implicitCast(cond, new TypeBool);
	return new While(cond, state);
}

Expression semantic1Impl(Parser.New that, Context context) {
	auto value = semantic1(that.value, context);
	return new New(value);
}

Expression semantic1Impl(Parser.NewArray that, Context context) {
	auto length = semantic1(that.length, context);
	auto value = semantic1(that.value, context);
	value = implicitCast(value, new TypeUInt(0));
	return new NewArray(length, value);
}

Expression semantic1Impl(Parser.Cast that, Context context) {
	return new CastFunc;
}

Expression semantic1Impl(Parser.Index that, Context context) {
	auto array = semantic1(that.array, context);
	auto index = semantic1(that.index, context);
	return dispatch!(semantic1Index, TypeMetaclass, TypeArray, TypeStruct, Type)(
			array.type, array, index, that.position);
}

Expression semantic1Index(TypeMetaclass type, Wrapper!Expression array,
		Wrapper!Expression index, Position position) {
	if (auto tuple = index.castTo!TupleLit) {
		if (tuple.values.length == 0) {
			return new TypeArray(array.castTo!Type);
		}
	}
	error("Array types must have an empty index", position);
	assert(0);
}

Expression semantic1Index(TypeArray type, Wrapper!Expression array,
		Wrapper!Expression index, Position position) {
	index = implicitCast(index, new TypeUInt(0));
	return new Index(array, index);
}

Expression semantic1Index(TypeStruct type, Wrapper!Expression array,
		Wrapper!Expression index, Position position) {
	auto indexLiteral = index.castTo!IntLit;
	if (!indexLiteral) {
		error("Expected integer when indexing tuple", position);
	}
	return new TupleIndex(array, indexLiteral.value.to!uint);
}

Expression semantic1Index(Type type, Wrapper!Expression array,
		Wrapper!Expression index, Position position) {
	error("Unable to index", position);
	assert(0);
}

Expression semantic1Impl(Parser.Call that, Context context) {
	auto calle = semantic1(that.calle, context);
	auto argument = semantic1(that.argument, context);
	return dispatch!(semantic1Call, TypeStructFunc, TypeCastFunc,
			TypeCastPartial, TypeMetaclass, TypeFunction, Type)(calle.type,
			calle, argument, that.position);
}

Expression semantic1Call(TypeStructFunc type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position) {
	auto tuple = argument.castTo!TupleLit;
	if (!tuple) {
		error("Struct expects a tuple", position);
	}
	return new TypeStruct(tuple.values.map!assumeType.map!(a => a._value).array);
}

Expression semantic1Call(TypeCastFunc type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position) {
	auto argumentType = assumeType(argument);
	return new CastPartial(argumentType.castTo!Type);
}

Expression semantic1Call(TypeCastPartial type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position) {
	return Wrapper!Expression(explicitCast(argument,
			Wrapper!Type(calle.castTo!CastPartial.value, position), position));
}

Expression semantic1Call(TypeMetaclass type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position) {
	auto argumentType = assumeType(argument);
	return new TypeFunction(calle.castTo!Type, argumentType);
}

Expression semantic1Call(TypeFunction type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position) {
	argument = implicitCast(argument, type.argument);
	return new Call(calle, argument);
}

Expression semantic1Call(Type type, Wrapper!Expression calle,
		Wrapper!Expression argument, Position position) {
	error("Unable to call", position);
	assert(0);
}

Expression semantic1Impl(Parser.Slice that, Context context) {
	auto array = semantic1(that.array, context);
	auto left = semantic1(that.left, context);
	auto right = semantic1(that.right, context);
	if (!array.type.castTo!TypeArray) {
		error("Slicing expects an array", that.position);
	}
	left = implicitCast(left, new TypeUInt(0));
	right = implicitCast(right, new TypeUInt(0));
	return new Slice(array, left, right);
}

//todo remove me
//wierd compiler bug

alias ParserBinary = Parser.Binary;
alias ParserPrefix = Parser.Prefix;

Expression semantic1Impl(string op)(ParserBinary!op that, Context context) {
	auto left = semantic1(that.left, context);
	auto right = semantic1(that.right, context);
	implicitCastDual(left, right, that.position);
	static if (["*", "/", "%", "+", "-", "<=", ">=", ">", "<"].canFind(op)) {
		if (!left.type.isInt || !right.type.isInt) {
			error(op ~ "only works on ints", that.position);
		}
	} else if (op == "~") {
		if (!left.type.castTo!TypeArray) {
			error(op ~ "only works on arrays", that.position);
		}
	} else if (["&&", "||"].canFind(op)) {
		left = implicitCast(left, new TypeBool());
	}
	return new Binary!op(left, right);
}

Expression semantic1Impl(string op)(ParserPrefix!op that, Context context) {
	auto value = semantic1(that.value, context);
	static if (op == "-") {
		if (!value.type.isInt) {
			error("- only works on ints");
		}
	} else static if (op == "*") {
		if (!value.type.castTo!TypePointer) {
			error("* only works on pointers");
		}
	} else static if (op == "&") {
		if (!value.lvalue) {
			error("& only works on lvalues");
		}
	} else static if (op == "!") {
		value = implicitCast(value, new TypeBool);
	} else static if (["+", "/"].canFind(op)) {
		error(op ~ " not supported", that.position);
	}
	return new Prefix!op(value);
}

Statement semantic1Impl(Parser.Statement that, Context context) {
	return dispatch!((that, context) => cast(Statement) semantic1(that, context)
			._value, Parser.ScopeVarDef, Parser.Assign, Parser.Expression)(that, context);
}

Expression semantic1Impl(Parser.Scope that, Context context) {
	auto searcher = new ScopeSearcher;
	context.searchSpace ~= searcher;
	Wrapper!Statement[] states;
	foreach (c, pstate; that.states) {
		auto state = semantic1(pstate, context);
		if (auto variable = state.castTo!ScopeVarDef) {
			searcher.variables[variable.name] = new ScopeVarRef(Wrapper!ScopeVarDef(variable,
					that.position));
			context.localVariables[variable] = Tuple!()();
		}
		states ~= state;
	}
	auto last = that.last ? semantic1(that.last, context) : Wrapper!Expression(new TupleLit(null));

	return new Scope(states, last);
}

ScopeVarDef semantic1Impl(Parser.ScopeVarDef that, Context context) {
	auto value = semantic1(that.value, context);
	if (that.explicitType) {
		auto explicitType = semantic1Type(that.explicitType, context);
		value = implicitCast(value, explicitType);
	}
	if (that.manifest) {
		error("Manifest locals not yet supported", that.position);
	}

	return new ScopeVarDef(that.name, value);
}

Assign semantic1Impl(Parser.Assign that, Context context) {
	auto left = semantic1(that.left, context);
	auto right = semantic1(that.right, context);
	if (!left.lvalue) {
		error("Not an lvalue", that.left.position);
	}
	right = implicitCast(right, left.type);

	return new Assign(left, right);
}

Expression semantic1Impl(Parser.StringLit that, Context context) {
	return new StringLit(that.value);
}

Expression semantic1Impl(Parser.ArrayLit that, Context context) {
	if (that.values.length == 0) {
		error("Array Literals must contain at least one element", that.position);
	}
	auto values = that.values.map!(a => semantic1(a, context));
	auto head = values.front;
	values.popFront;
	auto array = only(head).chain(values.map!(a => implicitCast(a, head.type))).array;
	return new ArrayLit(array);
}

Expression semantic(Parser.ExternJs that, Context context) {
	error("extern must be a global variable", that.position);
	assert(0);
}

Wrapper!Expression semantic1Extern(Parser.ExternJs that, string name, Context context) {
	return Wrapper!Expression(new ExternJs(name), that.position);
}
