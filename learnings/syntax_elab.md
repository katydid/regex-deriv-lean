# syntax_elab

We can use `syntax` and `elab` to create a custom syntax.
In this example we will create a custom syntax for our regular expression type:

```lean
inductive Regex (α: Type): Type where
  | emptyset : Regex α
  | emptystr : Regex α
  | pred : (p: α -> Prop) → [DecidablePred p] → Regex α
  | or : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
```

We create a special syntax category for our regular expression:

```lean
declare_syntax_cat regex
```

We follow this by declaring a bnf for our parsing our syntax: 

```lean
syntax "∅" : regex -- \ emptyset
syntax "ε" : regex -- \ eps
syntax char : regex -- char
syntax ident : regex -- string
syntax str : regex -- string
syntax regex " | " regex : regex -- or
syntax regex regex : regex -- concat
syntax regex "*" : regex -- star
syntax "(" regex ")" : regex -- parenthesis
```

Notice that `char`, `ident` and `str` can be used to create a regex of character predicates.
For this we will need some helper functions to create a concat expression for strings:

```lean
def mkChar (c: Char): Regex Char :=
  Regex.pred (· = c)

def mkList (chars: List Char): Regex Char :=
  match chars with
  | [] => Regex.emptystr
  | [c] => mkChar c
  | [a,b] => Regex.concat (mkChar a) (mkChar b)
  | _ => foldl (λ r c => Regex.concat r (mkChar c)) Regex.emptystr chars

def mkString (s: String): Regex Char :=
  mkList (s.toList)
```

Next we can create our elaborate function, that takes the parse tree for the regex and turns it into a Regex:

```lean
partial def elabRegex : Lean.Syntax → Lean.Meta.MetaM Lean.Expr
  | `(regex| ∅) => Lean.Meta.mkAppM ``Regex.emptyset #[]
  | `(regex| ε) => Lean.Meta.mkAppM ``Regex.emptystr #[]
  | `(regex| $c:char) => Lean.Meta.mkAppM ``mkString #[Lean.mkStrLit c.getChar.toString]
  | `(regex| $i:ident) => Lean.Meta.mkAppM ``mkString #[Lean.mkStrLit i.getId.toString]
  | `(regex| $s:str) => Lean.Meta.mkAppM ``mkString #[Lean.mkStrLit s.getString]
  | `(regex| $x | $y) => do
    let x ← elabRegex x
    let y ← elabRegex y
    Lean.Meta.mkAppM ``Regex.or #[x, y]
  | `(regex| $x $y) => do
    let x ← elabRegex x
    let y ← elabRegex y
    Lean.Meta.mkAppM ``Regex.concat #[x, y]
  | `(regex| $x*) => do
    let x ← elabRegex x
    Lean.Meta.mkAppM ``Regex.star #[x]
  | `(regex| ($x)) => elabRegex x
  | _ => Lean.Elab.throwUnsupportedSyntax
```

We are now doing meta programming, so the syntax is a little different from normal Lean:
* We do pattern matching on the regex tree using a backtick and `(syntax_category| node)`.
* We capture variable using a dollar.
* The `Lean.Meta.mkAppM` function takes a function and applies a list of paramters to it.
* The function parameter is passed with two backticks to escape the name and the list is passed with a hashtag to escape it and distinguish it from a normal list.

Finally we can hook it all up using `elab`:

```lean
elab " ~ " e:regex " ~ " : term => elabRegex e
```

we have specific the tilde character as a way to distinguish between lean syntax and our special syntax.
We can now use our new syntax:

```lean
example: Regex Char := ~ 'a' ~
example: Regex Char := ~ a ~
example: Regex Char := ~ abc ~
example: Regex Char := ~ 'a''b''c' ~
example: Regex Char := ~ "" ~
example: Regex Char := ~ a ~
example: Regex Char := ~ "a" ~
example: Regex Char := ~ ab ~
example: Regex Char := ~ "ab" ~
example: Regex Char := ~ abc ~
example: Regex Char := ~ "abc" ~
example: Regex Char := ~ abc ~
example: Regex Char := ~ "abc" ~
example: Regex Char := ~ 'a' ~
example: Regex Char := ~ a ~
example: Regex Char := ~ 'a' | 'b' ~
example: Regex Char := ~ ab ~
example: Regex Char := ~ a b ~
example: Regex Char := ~ a b c ~
example: Regex Char := ~ a* ~
example: Regex Char := ~ (a)* ~
example: Regex Char := ~ "a"* ~
example: Regex Char := ~ ("a")* ~
example: Regex Char := ~ (a)(b) ~
example: Regex Char := ~ (a | b)* ~
```
