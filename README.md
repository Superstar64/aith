Aith is a toy language that compiles to javascript.
Aith uses basic hindly milner with qualified types for type inference, entire functions can be inferred without type annotations.
Aith has referential transparency up to non termination, if your programs halts, it's referentially transparent.
Aith has linear types, which are use once types. As of how, linear types are only used to preserve referential transparency.
Eventually, linear types will be used to handle memory management when a C backend is added.
Aith functions require a `world` type to preform side effects, and said world must be used linearly.
Aith has a lambda calculus style macros system on terms. Macros will be beta reduced before code generation.
Aith's kind system prevent macro types from escaping into runtime types.

This language is not yet intended for practical use.

	# is used for single line comments
	#{ #} is used for multiline comments

Aith's types:

	world # type need for io actions, must be used linearly
	boolean # boolean type
	character # character type, utf-32
	integer # signed integer type, platform dependent size
	integer8
	integer16
	integer32
	integer64
	natural # signed natural type, platform dependent size
	natural8
	natural16
	natural32
	natural64
	(& t, t',t''... &) # tuple type
	raw t* # pointer type
	raw t[] # array type
	unique t* # owning pointer, must be used linearly, currently unused
	unique t[] # owning array, must be used linearly, currently unused
	t -> t' # function type
	t ~> t' # macro type, as of now, always linear
	<x,x'> t # generic type, where x and y are type variables in t
	<x extends c & c'> t # constrainted generic type by c and c'

Owner pointers and owner arrays are only used for allocating, they must be borrowed to perform other actions on.

Aith's kinds:
	runtime # kind of runtime type
	k ~*> k' # kind of macro

For all types except macro types, all sub-types must be of kind runtime.
All kinds are currently infered only, with no user supplied annotations.


Aith's constraints:

	equal # comparable types
	number # numeric types
	unrestricted # non linear types
	has n : t # tuple with element t at index n
	
Aith's builtin functions:

	new : ~ <a extends unrestricted> a ~> world ~> (& raw a*, world &) ~ # copy a value to the heap
	new array : ~ <a extends unrestricted> natural ~> a ~> world ~> (& raw a[] , world &) ~ # creates an array given a and and default value
	cast : <a extends number, b extends number> a ~> b # integer casting
	length : ~ <a> raw a[] ~> natural ~ # length of array
	
Aith's expressions:
	p => e # macro literal, p is a pattern match
	p { e } # macro literal
	x = e; e' # let in expression, x is set to e in e', e must be of kind runtime
	x # variable
	1 # integer literals
	'a' # character literals
	"a" # string literals, returns owner array of characters
	true # boolean literals
	false
	(e) # parenthesis
	(e,e',e'',...) # tuple literals, length must not be 1
	if e { e' } else { e'' }" # if expression, e requires parens if it contains operations
	e:t # expression type annotation,x is an expression, t is a type
	e(e') # macro call
	e` # convert runtime function into macro
	e.e' # right to left macro call, calls e' with e
	e[e'..e''] # slice expression, e' and e'' must be of type natural 0
	[e, e', e''] # array literals
	e_x # tuple index e is the tuple, x an integer literal
	e&*_x # tuple forward, given e is a pointer to tuple return a pointer to a sub element
	math/logic binary operators(in order of precedence by row): both left and right sides must be the exact same type
		"*","/","%",
		"+","-"
		"==","!=","<=",">=","<",">",
		"&&","||",
	math/logic prefix operators:
		"-","!"
	e[e'] # array index expression, e' must be of natural 0, side effect
	*e # deference a pointer, side effect
	e <- e' # assign a value to a pointer, e must be a pointer, side effect
	import "path" # import a module
	m::x  # access module field, where m is a module and x is a field inside of a module
	do => e # do expression
	do { e }
	try => # try expression
	try { e }
	run e; e' # run expression
	extern "abc" # extern expression, must be inside extern global state

`e[e']`, `*e`, and `e <- e` are side effects, they return a macro of type `world ~> (& t , world &)`

Aith's has an expression based do notation. As of now do notation only desugars into a state monad(terms of type `world ~> (& t , world &)`).
`do { e }` takes a pure `e` with some `try` sub expressions and wraps e in a state monad while apply the effects.
`try { e }` contain side effects and are moved outside their surrounding corrisponding do expression. 
`run e; e'` is the equivalent of `() = try { e }; e'`.
Currently do expressions don't work well with `if` expressions.


Aith's pattern matches:
	x # named pattern match, x must of kind runtime
	~x # lazy named pattern match, x may be any stage
	(p,p',p'') # tuple pattern match, cannot have lazy pattern matches
	|x| # shadowing pattern match, shadow previously declared variables
	~|x| # shadowing lazy pattern match
	
Aith's global statements:

	inline x = e;  # declare a global that in inlined everywhere that it's used
	~ t ~ inline x = e; # typed inline global
	symbol x = e; # declare and convert a macro into a global function, `e` must be of type `t ~> t'`
	~ t ~ symbol x = e; # typed symbol global, the type must be a function, `t -> t'`
	template x = e; # similar to symbol, except e may have a polymorphic type, will be different when C code generation gets added
	~ t ~ template x = e;
	~ t ~ extern x = e; # extern global, e must of an extern expression

