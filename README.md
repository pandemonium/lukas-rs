Marmelade is a functional programming language in the spirit of the ML family.

It supports System F with algebraic data types. Has pattern matching and string interpolation. It is actively developed and at this point I am adding type class support.

## Native-backend targets and capabilities

Foreign values state the capability they consume at the implementation boundary:

```lady
foreign [ Browser; Dom ] document_title :: Unit -> Text
foreign [ Socket ] connect :: Text -> Int -> Connection
```

Ordinary Marmelade values have no annotation. The compiler infers their requirements
transitively, starting at `Root.start`, and rejects a build before C emission when a
reachable requirement has no provider for the selected target. Unreachable foreign
values do not constrain an application.

The native backend has five explicit targets in addition to the current-host alias:

| Profile | Platform root | Output |
| --- | --- | --- |
| `host` | current macOS, Linux, or Windows host | native process |
| `native-macos` | `Native_MacOS` | native process |
| `native-linux` | `Native_Linux` | native process |
| `native-windows` | `Native_Windows` | native process |
| `wasm-node` | `Wasm_Node` | Emscripten ES module and Wasm |
| `wasm-browser` | `Wasm_Browser` | Emscripten ES module, Wasm, and page |

For example:

```sh
./compile-lady.sh --backend native --profile wasm-browser \
  ladies/examples/01_literals_and_operators

./compile-lady.sh --backend native --profile wasm-node \
  ladies/examples/01_literals_and_operators
node build/01_literals_and_operators/node/run.mjs
```

Browser output is written to `build/<program>/browser/`. Serve that directory over
HTTP and open `index.html`. The generated module exports `_marmelade_start`; the
page connects standard output to a `<pre>` and calls the entry point. Node output is
written to `build/<program>/node/` and includes `run.mjs`. Wasm builds are currently
single-threaded.

The provider graph lives in `ladies/stdlib/capabilities.conf`. Consumers name
capabilities such as `Timer`, `Fetch`, `Socket`, and `Web_Socket`. Each provider says
which capability it implements, which other capabilities or platform root it needs,
and which C definitions or implementation sources the build must use. Multiple
providers are alternatives, while the requirements of one provider are all required:

```text
provider Browser_Web_Socket provides Web_Socket requires Browser defines MARM_PROVIDER_WEB_SOCKET_BROWSER
provider Socket_Web_Socket provides Web_Socket requires Socket,Timer defines MARM_PROVIDER_WEB_SOCKET_SOCKET
```

Set `LADY_CAPABILITIES` to use another graph. Each build writes its selected providers
to `build/<program>/providers-<profile>.txt` and the inferred per-symbol requirements
to `build/<program>/requirements-<profile>.txt`. For an explicit native target that
differs from the current machine, set `CC` to the appropriate cross compiler. The
Scheme backend keeps its existing behavior and does not read or enforce this model.

This is a summary of all the things that work currently.

```List ::= ∀α. Nil | Cons α (List α)

Perhaps ::= ∀α. Nada | This α

head :: ∀α. List α -> Perhaps α := λxs.
  deconstruct xs into Cons x tail -> This x | Nil -> Nada

fold_right :: ∀z α. (α -> z -> z) -> z -> List α -> z := λf z xs.
    deconstruct xs into
      Cons a tail -> f a (fold_right f z tail)
    | Nil         -> z

map :: ∀α β. (α -> β) -> List α -> List β :=
  λf xs. fold_right (λx tail. Cons (f x) tail) Nil xs

bind :: ∀α β. (α -> List β) -> List α -> List β :=
  λf. fold_right (λx. append (f x)) Nil

append :: ∀α. List α -> List α -> List α :=
  λxs ys. fold_right Cons ys xs

length :: ∀α. List α -> Int :=
  λxs. fold_right (λa tail. 1 + tail) 0 xs

Result ::= ∀a e. Return a | Fault e

id :: ∀α. α -> α :=
  λx. x

flip :: ∀α β r. (α -> β -> r) -> β -> α -> r :=
  λf b a. f a b

compose :: ∀α β γ. (β -> γ) -> (α -> β) -> α -> γ :=
  λg f a. g (f a)

fibonacci :: Int -> Int := λn.
  if n = 0 or n = 1 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

clamp := lambda from to.
  fibonacci from, fibonacci to

frobnication :=
  deconstruct clamp 3 5 into
    p, q -> p * q

order_number := This 66
order_number :: Perhaps Int := This 66

switch := lambda x.
  deconstruct
    x
  into
    1         -> "Eins"
  | 2         -> "Zwei"
  | otherwise -> "Polizei"

Dollars ::=
  { The_Good :: Int
    The_Bad  :: Text
    The_Ugly :: Perhaps Int
  }

make_one := lambda good bad.
  { The_Good: good; The_Bad: bad; The_Ugly: Nada }

dollars :: Text :=
  deconstruct
    make_one 1 "Sylvester"
  into
    { The_Good: good; The_Bad: bad; The_Ugly: This ugly } ->
        "`good`, `bad`, `ugly`"
  | { The_Good: good; The_Bad: bad; The_Ugly: Nada }       ->
        "`good`, `bad`"

print_scientific_fact := lambda icewalls.
  print_endline if icewalls
    then "Earth has an interesting shape"
    else "Our princess is in another castle"

compute_earthiness := λr.
  let π = 3 in 4/3 * π * r * r * r

puts :: Text -> Unit := λs. print_endline s

einstein :: Int -> Int -> Int := lambda m c.
  let square = λc. c * c in m * square c

whence :: forall a. Bool -> (Unit -> a) -> (Unit -> a) -> a :=
  lambda predicate consequent alternate.
    if predicate then consequent () else alternate ()

factorial := lambda x.
  if x = 0 then 1
  else x * factorial (x - 1)

fibonacci :: Int -> Int := λn.
  if n = 0 or n = 1 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

divide := lambda dividend divisor.
  if divisor = 0
  then Nada
  else This (dividend / divisor)

good_times :: forall e. Result Int e :=
  Return 10

bad_times :: forall a. Result a Text :=
  Fault "you know I've had my share"

Arithmetic_Error ::= Division_by_Zero | NaN

divide2 :: Int -> Int -> Result Int Arithmetic_Error := lambda dividend divisor.
  if divisor = 0 then Fault Division_by_Zero
  else Return (dividend / divisor)

start := λ_.
  print_endline "Hello, world"

  let the_thing = (1 + 68) * 840 / 2 in
  let text = show the_thing
  in print_endline text

  let the_king_weareth_clothing = false in
  whence the_king_weareth_clothing
    (λ_. print_endline "for it is true")
    (λ_. print_endline "you better believe!")

  print_endline "7 factorial: `factorial 7` and 7 fibonacci: `fibonacci 7`."

  let thang = 1, 2, "and to the 4"
  in print_endline "`thang.0`, `thang.1`, `thang.0 + thang.1` `thang.2`"

  let show_perhaps = λp.
    deconstruct p into
      Nada   -> "Division by zero"
    | This x -> show x
  in print_endline "4 / 2 is `show_perhaps (divide 4 2)` but 4 / 0 is `show_perhaps (divide 4 0)`."

  let show_arithmetic_error = λe.
    deconstruct e into
      NaN -> "Not a number"
    | Division_by_Zero -> "Also Division by zero"
  in let show_result = λr.
    deconstruct r into
      Return a -> show a
    | Fault e  -> show_arithmetic_error e
  in print_endline "4 / 2 is `show_result (divide2 4 2)` but 4 / 0 is `show_result (divide2 4 0)`."

  print_endline "switch(2) -> `switch 2` and switch(7) -> `switch 7`"

  let another_thing = 1 in another_thing + 2
```
