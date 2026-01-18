# Functional Marmelade

# Me

1. Patrik Andersson. Compulsively drawn to things--especially those that I don't fully understand. Such as programming.

Started out an expert in Java, that went on for about a decade.

Then I Continued as a very humbled functional programmer, starting with Scala but with regular pitstops at Saloons such as Haskell, Category Theory, meeting the usual suspects, such as OCaml, Domain Driven Design and parsing. Not validating.

Now living the Curry Howard-fantancy of types as proofs.

# Why

1. Curiosity, Rust and ¬impossible.

Unbounded curiousity, and for the longest time, I really wanted to learn and become really good at Rust. The one way I know that makes these kinds of things happen is by trying something that is difficult, but not impossible.

I wanted to implement a type checker, which seemed too hard, and a pattern matcher because that clearly functions through arcane magic, and I wanted a language with currying and functions as values.

I wanted the experience of being the jungle monkey presented a mobile phone.

# Recipe

1. sudo Make me a functional language.

(Make a bullet list of these properties.)

Marmelade is a functional programming language in the spirit of the MLs, with currying, pattern matching, first class lambdas, type polymorphism and type inferencing. It uses a bidirectional type checker.

# Resources

https://github.com/pandemonium/marmelade
https://github.com/pandemonium/lukas_rs

# The Marmelade Language

Writing programs offers few surprises. We even spell Hello, World the same way.

start := lambda x.
  print_endline "Hello, world"

start :: Int -> ... := lambda x.
  print_endline "Hello, world"

start :: Int -> exists a. a := lambda x.
  print_endline "Hello, world"


No type annotations are needed, they are inferred.

let the_thing = (1 + 68) * 840 / 2 in
let text = show the_thing
in print_endline text

the_thing :: Int
text :: Text
show :: ∀α. α -> Text
print_endline :: Text -> Unit


Functions, mildly inspired by The Lambda Calculus

print_scientific_fact := lambda x.
  let the_thing = (x + 67) * 840 / x in
  let text =
    show the_thing
  in print_endline text

compute_and_print := λfactor.
  print_scientific_fact factor


Top-level values can be annotated with a type signature

computation :: Int -> Int :=
  λfactor.
    let the_thing = (factor + 68)
    in
        840 / (1 + factor)

core_business_logic :: Int -> Int -> Int := lambda p q.
  let the_thing = (1 + p)
  in
    Logger.info "Doing logics with `p` and `q`"
    q / 2


If expressions ought to be sufficient for everyone

factorial := lambda x.
  if x = 0
  then 1
  else x * factorial (x - 1)

fibonacci :: Int -> Int := λn.
  if n = 0 or n = 1 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)


Algebraic data types -- tuples

let thang =
  1, 2, "and to the 4"
in print_endline "`thang.0`, `thang.1`, `thang.0 + thang.1` `thang.2`"

clamp := lambda from to.
  fibonacci from, fibonacci to

frobnication :=
  deconstruct clamp 3 5 into
    p, q -> p * q


Algebraic data types -- A fistful of Co-products

Perhaps ::= forall a. This a | Nah

order_number := This 66
order_number :: Perhaps Int := This 66

divide :: Int -> Int -> Perhaps Int :=
  lambda dividend divisor.
    if divisor = 0
    then Nah
    else This (dividend / divisor)


ADTs -- For a few Co-products more

Result ::= ∀a e. Return a | Fault e

Artithemtic_Error ::= Division_by_Zero | NaN

good_times :: forall e. Result Int e :=
  Return 10

bad_times :: forall a. Result a Text :=
  Fault "you know I've had my share"

divide :: Int -> Int -> Result Int Artithemtic_Error :=
  lambda dividend divisor.
    if divisor = 0
    then Fault Division_by_Zero
    else Return (dividend / divisor)


ADTs -- Look ma, we have records

Dollars ::=
  { The_Good :: Int
    The_Bad  :: Text
    The_Ugly :: Perhaps Int
  }

make_one := lambda good bad.
  { The_Good: good; The_Bad: bad; The_Ugly: Nah }

make_another := lambda good bad ugly.
  { The_Good : good
    The_Bad  : bad
    The_Ugly : This ugly
  }


Pattern matching

switch := lambda x.
  deconstruct x into
    1         -> "Eins"
  | 2         -> "Zwei"
  | otherwise -> "Polizei"

switch :: Int -> Text

sovereign_citizen := lambda x.
  deconstruct x into
    1         -> "Am I being detained?"
  | "2"       -> "Am I free to go?"
  | otherwise -> "Polizei"

$$$$ type error: 138:5: cannot unify
       left:  Text
       right: Int


Algebraic data types -- pattern matching

dollars :=
  deconstruct
    make_one 1 "Sylvester"
  into
    { The_Good: good; The_Bad: bad; The_Ugly: This ugly } ->
    "`good`, `bad`, `ugly`"
  | { The_Good: good; The_Bad: bad; The_Ugly: Nah }       ->
    "`good`, `bad`"


Algebraic data types -- pattern matching

dollars :=
  deconstruct make_one 1 "Sylvester" into
    { The_Good: good; The_Bad: bad; The_Ugly: This ugly } -> ugly

$$$$ type error: 95:3: deconstruction does not cover all of `Root::make_one 1 Sylvester`; remaining: The_Good: () The_Bad: () The_Ugly: Nope


Algebraic data types -- pattern matching

dollars :=
  deconstruct make_one 1 "Sylvester" into
    otherwise -> 10
  | { The_Good: good; The_Bad: bad; The_Ugly: This ugly } -> ugly

$$$$ type error: 97:5: case { { The_Good: good; The_Bad: bad; The_Ugly: Nope } } is not useful for Root::make_one 1 Sylvester.


Curry! Curry! Curry!

compute_and_print := λfactor.
  print_scientific_fact factor

compute_and_print :=
  print_scientific_fact

print_scientific_fact :: Int -> Unit := ...

compute_and_print :: Int -> Unit := print_scientific_fact

map :: ∀a b. (a -> b) -> Perhaps a -> Perhaps b

dollars_from_sek := lambda sek. 11 * sek

map dollars_from_sek (This 5)

dollar_map :: Perhaps Int -> Perhaps Int :=
  map dollars_from_sek

sek := dollar_map (This 7)


Lambdas. We have already seen them!

All functions in Marmelade are lambda expressions.

say_name := lambda name.
  "My name is; my name is: `name`, ..."

also_say_name := say_name

say_it :=
  also_say_name

say_real_name := lambda fake real.
  print_endline "Formerly known as `say_it fake` but akshually `also_say_name real`"


I accidentally a text interpolator

any_expression := 420

and_function := λn. n * any_expression + 1

let render = λx. "I, `x`, can be anything `and_function any_expression / 69`." in
print_endline "... when I say the name, Biggus: `render "Optimus Prime"`?"


Let's make a list, shall we?

IntList ::= Nil | Cons Int List

TextList ::= Nil | Cons Text List

List ::= forall a. Nil | Cons a (List a)

List ::= ∀α. Nil | Cons α (List α)

tail := lambda xs.
  deconstruct xs
  into Cons x tail -> tail | Nil -> Nil

head := λxs.
  deconstruct xs
  into Cons x tail -> x | Nil -> ...(now what?)


Let's do some functional computer programming

Perhaps ::= ∀α. Nope | This α

head :: ∀α. List α -> Perhaps α := λxs.
  deconstruct xs
  into Cons x tail -> This x | Nil -> Nope

head (Cons 1 Nil)
#### This 1 :: Perhaps Int

head Nil
#### Nope :: ∀α. Perhaps α

map :: ∀α β. (α -> β) -> List α -> List β := λf xs.
  deconstruct xs into
    Cons x xs -> Cons (f x) (map f xs)
  | Nil -> Nil

length :: ∀α. List α -> Int := λxs.
  deconstruct xs into
    Cons x xs -> 1 + length xs
  | Nil -> 0

Lots of repeated structure.


Use the folds, Lukas

fold_right :: ∀z α. (α -> z -> z) -> z -> List α -> z :=
  λf z xs.
    deconstruct xs into
      Cons a tail -> f a (fold_right f z tail)
    | Nil         -> z

map :: ∀α β. (α -> β) -> List α -> List β :=
  λf xs. fold_right (λx tail. Cons (f x) tail) Nil xs

length :: ∀α. List α -> Int :=
  λxs. fold_right (λa tail. 1 + tail) 0 xs


Golf all the things! ETA reduction to the rescue

map :: ∀α β. (α -> β) -> List α -> List β :=
  λf xs. fold_right (λx tail. Cons (f x) tail) Nil xs

map :: ∀α β. (α -> β) -> List α -> List β :=
  λf. fold_right (λx tail. Cons (f x) tail) Nil

map :: ∀α β. (α -> β) -> List α -> List β :=
  λf. fold_right (λx. Cons (f x)) Nil

map :: ∀α β. (α -> β) -> List α -> List β :=
  λf. fold_right (compose Cons f) Nil

length :: ∀α. List α -> Int :=
  fold_right (λa z. 1 + z) 0


One more thing!

System F-style language with let polymorphism:

let f = λx. x in
f 1, f "hi", f true

i.e.: it infers f to be ∀α. α -> α

# Architecture

## Lexical Analyzer

lex :: List char -> List Token

Token ::=
  { Type     : Token_Type
    Location : Source_Location
  }

Token_Type ::=
    Type_Assign
  | Arrow
  | Identifier Text
  | Keyword    Keyword
  | Star | Gte | Plus
  ...

Recognizes prefixes of the input stream as different classes of information, playfully referred to as tokens. Also keeps track of positions--logical locations on a sheet of grid paper.

Recognition is subtle; parsing strings, comments and even identifier names is not hard in any real sense, but Marmelade is layout sensitive so it falls on the lexing phase to understand the concept of offside rules.

We refer to the exact way one token follows another in one of the following way:

Empty, Indent, Dedent and Newline.

Empty just means that it succeeds it, with or without some sort of whitespace.

The rest is all about splitting hairs so that the parser can understand what block some continuation of an expression belongs to. This token is on the next line, but is it to the left, right or simply underneeth?


## Parser

parse :: List Token -> Result Compilation_Unit Parse_Error

Parse_Error ::=
    Unexpected_Token Token
  | Expected_Token_type Token_type
  ...

Parsing is understanding what a stream of seemlingly unrelated pieces of information, actually mean when taken as a whole. A sense maker or sorts.

Parsing according to a grammar, a specification for what some sequence of words actually mean, produces another type of information unit often referred to as an Abstract Syntax Tree. Or AST.

The grammar can be thought of as individual functions like:

parse_declarations :: List Token -> Parse_Result (List Declaration)

parse_declaration :: List Token -> Parse_Result Declaration :=
  lambda input.
    deconstruct input into
      Token (Token_Type.Identifier id) position : Token Token_Type.Equals * : remains ->
    parse_value_binding id None position remains
    | ... => ...

parse_value_binding ::
Text ->
Option Type_Signature ->
Source_Location ->
List Token ->
Parse_Result Declaration =
lambda id type_signature position remains.
..

Parse_Result is central to the literal parsing automat. Its definition is something like:

Parse_Result ::= forall a.
alias Result (a, List Token) Parse_Error

Which is to say: Parse_Result is the ultimate parsing effect. It is either the parsed production together with the remaining input or it is a value that describes why the parser was unable to make progress.

Marmelade has infix expressions which is to say that it has a semantic much akin to arithmetic. Saying:

net*salary = invoice_amount / get_vat Vat.Normal - gross_salary * AGA*fraction - gross_salary * salary_tax

Does what we wish that it must do. I solve this using a technique colloquially termed Pratt parsing.

### Pratt Parsing

parse_expression, parse_expression_prefix, parse_expression_infix

## Type inferencer

infer :: Expression -> Typing_Context -> Result Type_Inference Type_Error

Typing_Context ::=
{ Bindings :: Map Binding Type
}

Type ::=
Int
| Co_product (List (Identifier, Type_Expression))
| Arrow Type Type
| Parameter Type_Parameter
...

Type_Error ::=
Undefined_Symbol Identifier
| Incompatible_Coproducts Co_product Co_product
| Unify_Impossible Type Type
...

## Type inferencing / type synthesis

Synthesising types for things that the typer knows about. Scalar literals, functions, co-products and products.

Describe:

1. inferring and checking the type of an if expression
2. inferring and checking the type of an application

3. unification
   Create this information from thin air.

4. substitutions

Inferring types by assigning a fresh type parameter to something.

## Type checker

check :: Type -> Expression -> Typing_Context -> Result () Type_Error

Type_Error ::=
Expected_Type Type Expression
...

## Interpreter

reduce :: Expression -> Environment -> Result Value Runtime_Error

Expression ::=
Variable Identifier
| Int i64
| Lambda Identifier Expression

Environment ::=
{ Bindings :: Map Identifier Value
}

Value ::=
Int i64
| Co_product Identifier Value
| Closure Closure

Closure ::=
{ Parameter :: Identifier
Capture :: Environment
Body :: Expression
}

# Intentions

## Parse expressions

### Pratt-parsing

### Layout based

## Type expressions

## Check types
