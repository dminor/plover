Schönfinkel
===========

Schönfinkel is a little language written as a exercise to learn more about type
checking and type inference. It is third in a series of interpreters
I've been working on. The first,
[Scoundrel](https://github.com/dminor/scoundrel) was a purely functional
subset of Lua, written to learn more about Rust and interpreters in general.
It worked by evaluating the abstract syntax tree. The second,
[Walden](https://github.com/dminor/walden), a Smalltalk/Self dialect,
added a virtual machine and mutable state.

To keep things interesting Schönfinkel uses parser combinators rather than a
separate lexer and recursive descent parser like in Scoundrel and Walden. I
probably should have learned to use an existing parser combinator library
before trying to roll my own, the implementation ended up a bit messy.

The language is purely functional. Schönfinkel uses Hindley-Milner style type
inference. This was an evolution. The first implementation did limited, hard
coded type inference based upon operator types, which worked while the
language remained simple. I then took a break, learned about
[unification](https://en.wikipedia.org/wiki/Unification_(computer_science)) by
writing [Tern](https://github.com/dminor/tern) and came back. Essentially,
the type inference works by assigning types to every node in the abstract
syntax tree, generating constraints based upon how the nodes are used, and then
uses unification solve these constraints to determine types. For example, in
an if/then/else statement, the value in the *if* test must be a boolean, and
the types in the *then* and *else* branches must match.

Schönfinkel was much more time consuming to write than Scoundrel or Walden,
and I ended up taking a eight month break in between getting the initial
interpreter working, and coming back to redo type inference with unification
and add user data types. With type inference and a virtual machine, adding a
new language feature requires parser work, type inference work, and code
generation, which slowed down the development cycle and made it hard to keep
momentum on the project. It's a lot of fun to see a new part of a language come
alive in an interpreter, and that was a lot slower in Schönfinkel.

The language is named after
[Moses Schönfinkel](https://en.wikipedia.org/wiki/Moses_Sch%C3%B6nfinkel), a
logician.

Keywords
--------

The following are reserved keywords: *def*, *else*, *elsif*, *end*, *false*,
*fn*, *if*, *match*, *then*, *true*, *type* and *when*.

Values
------

### Boolean

Booleans take the values `true` and `false`. The usual boolean operators are
supported: `&&`, `||`, and `~` (for not).

### Datatypes

New types can be introduced by using the type statement:

```
type AorB := A | B end
```

Type variants can optionally take arguments:

```
type Option := Some x | None end
```

In this case, a constructor function is generated that takes an argument and
returns an instance of the type.

### Function

A function is a value consisting of a single argument, which may be a tuple,
and a body which is evaluated when the function is called.

```
fn (a, b, c) ->
    a + b + c
end
```

Lexical closures are supported and it is possible for a function to return another
function:

```
def adder := fn t -> fn x -> x + t end end
def f := adder 1
f 2
```

Functions can optionally take a name which is defined inside the body to allow
for recursive calls.

```
fn fact n ->
    fn iter (n, acc) ->
        if n == 0 then
            acc
        else
            iter(n - 1, n*acc)
        end
    end
    iter (n, 1)
end
```

Closures are implemented by finding *upvalues* by searching for variables that
live on the stack when the function is defined and copying them into an
environment for later use. The implementation was inspired by Lua.

### Number

Numbers are 64 bit integers. The usual arithmetic and comparison operators
are supported: `+`, `-`, `*`, `/`, `%`, '<', '<=', '==', '<>', '>', and '>='.
Division by zero results in a runtime error.

```
2 + 3 / 4 * 5 % 6
```

### Tuple

Tuples are a fixed size comma-separated list of other values:

```
(2, false, fn x -> x + 1 end, (1, 2))
```

Expressions
-----------

### If/Then/Elsif/Else/End

If expressions are used to evaluate conditionals. The else clause is
non-optional because every expression must return a value.

```
if x == 0 then
    0
elsif x == 1 then
    1
elsif x == 2 then
    2
else
    3
end
```

### Define

Define expressions are used to introduce variables. All variables are
immutable, but it is possible to shadow a previous define expression. The
value of a define expression is the value that is assigned to the variable.

```
def x := 1
def x := false
def y := def z := 42
```

### Function Calls

A function call consists of a function value followed by the value to which the
function is applied.

```
fn f x -> x + 1 end
f 1
```

Anonymous functions can be called by placing a value next to the function
definition.

```
fn x -> x + 1 end 1
```

This is not allowed for named functions, as it leads to syntactical oddities, for
instance:

```
fn f x -> x + 1 end
f 1
```

would be interpreted as trying to call f with itself as an argument, rather than a
separate definition and function call.

### Match/When/End

A match expression allows for code to be executed based upon which variant was used
to construct a datatype.

```
type Pair := Cons (a, b) | Null end

def list := Cons (1, Cons (2, Cons (3, Null)))

fn len xs ->
  match xs with
    Null -> 0
    | Cons (x, xs) -> 1 + len xs
  end
end

len list

```

The implementation relies upon two extra instructions in the virtual machine,
TypeEq, which checks which variant was used to build a datatype, and ExtVal,
which extracts the value from the datatype and pushes it to the stack. Variants
that have parameters are treated like function calls to create a new
environment for the parameters.

The type checking is fairly straightforward. Each variant in a match statement
must be of the same datatype. All variants of a datatype must also be
covered in the match expression. The condition must resolve to a datatype.
Using unification for type checking makes this easy, but it would have been
unmanageable using my original, handcoded type checker.

Todo
----
Although Schönfinkel was interesting and challenging to work on, it was not as
much fun as the other interpreters I've done. So it's unlikely that I'll ever
get around to any of these.
* Tail call elimination
* Replace vm with
[Cranelift](https://github.com/bytecodealliance/wasmtime/tree/master/cranelift)
or
[Inkwell](https://github.com/TheDan64/inkwell) code generation.
* Replace hand written parser with proper library. Maybe [Peg](https://crates.io/crates/peg)?
