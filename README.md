Typi is a toy language with a native language look and feel that compiles to javascript. 
This language is not intended for practical use.

Typi uses basic hindly milner for type inferance, entire functions can be inferred without type annotations.

Typi has linear types, which are use once types. As of how, linear types prevent double free and forget to free, but unsafe borrowing is still used.

Typi functions require a `world` type to preform side effects, and said world must be used linearly.

	# is used for single line comments
	#/ /# is used for multiline comments

Typi's types:

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
	"natural32
	natural64
	(& t, t',t''... &) # tuple type
	t(*) # pointer type
	t[*] # array type
	t(!) # owning pointer, must be used linearly
	t[!] # owning array, must be used linearly
	t -> t' # function type
	<x,x'> t # generic type, where x and y are type variables in t
	<x extends c & c'> t # constrainted generic type by c and c'

Owner pointers and owner arrays are only used for allocating, they must be borrowed to perform other actions on.

Typi's constraints:

	equal # comparable types
	number # numeric types
	unrestricted # non linear types
	has n : t # tuple with element t at index n
	
Typi's builtin functions:

	new : <a> (& a,world &) -> (& a(!), world &) # copys a value to a new heap pointer and returns it
	delete : <a> (& a(!),world &) -> (& a, world &)
	borrow : <a> a(!) -> (a(*), a(!) # unsafely borrow a pointer
	
	new array : <a extends unrestricted> (& natural, a &) -> a[!] # creates an array given a and and default value
	borrow array : <a> a[!] -> (a[*], a[!]) # borrow an array
	delete array : <a> a[!] -> (&&) # deletes the owner array
	
	cast : <a extends number, b extends number> a -> b # integer casting
	length : <a> a[*] -> natural # builtin length function
	index address : <a> (& a[*], natural, world) -> (& a(*), world &) # get pointer to array index
	assign : <a extends unrestricted> (& a(*), a, world &) -> world # assign value to pointer
	
Typi's expressions:

	p => e # function literal, p is a pattern match, as of now only global functions are supported
	p { e } # function literal
	x = e; e' # let in expression, x is set to e in e'
	x # variable
	1 # integer literals
	'a' # character literals
	"a" # string literals, returns owner array of characters
	true # boolean literals
	false #
	(e) # parenthesis
	(e,e',e'',...) # tuple literals, length must not be 1
	if e { e' } else { e'' }" # if expression, e requires parens if it contains operations
	e:t # expression type annotation,x is an expression, t is a type
	e(e') # function call
	e.e' # right to left function call, calls e' with e
	e[e'] # array index expression,e' must be of natural 0
	e[e'..e''] # slice expression,e' and e'' must be of type natural 0
	[e, e', e''] # array literals, expects an unrestricted type and returns an owner array
	e_x # tuple index e is the tuple, x an integer literal
	e&*_x # tuple forward, given e is a pointer to tuple return a pointer to a sub element
	math/logic binary operators(in order of precedence by row): both left and right sides must be the exact same type
		"*","/","%",
		"+","-"
		"==","!=","<=",">=","<",">",
		"&&","||",
	math/logic prefix operators:
		"-","!"
	*e # deference a pointer
	import "path" # import a module
	e::x  # access module field where e is a module and x is a field inside of a module

Typi's pattern matches:

	x # named pattern match
	(p,p',p'') # tuple pattern match
	|x| # shadowing pattern match, shadow previously declared variables
	
Typi's global statements:

	x = e  # declare a global
	x = t  # declare a type
	~ t ~ x = e"  # declared a typed global

