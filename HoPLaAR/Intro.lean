/-
Copyright (c) 2003-2007, John Harrison
Copyright (c) 2021, Shing Tak Lam
(See "LICENSE" for details)
-/

import HoPLaAR.Lib
import HoPLaAR.Aux.Result

inductive Expression
| Var (s : String)
| Const (n : Int)
| Add (e₁ e₂ : Expression)
| Mul (e₁ e₂ : Expression)
deriving Repr, Inhabited

namespace Expression

-- (* ------------------------------------------------------------------------- *)
-- (* Trivial example of using the type constructors.                           *)
-- (* ------------------------------------------------------------------------- *)

#check Add (Mul (Const 2) (Var "x")) (Var "y")

-- (* ------------------------------------------------------------------------- *)
-- (* Simplification example.                                                   *)
-- (* ------------------------------------------------------------------------- *)

def simplify₁ : Expression → Expression
| Add (Const n) (Const m) => Const (n + m)
| Mul (Const n) (Const m) => Const (n * m)
| Add (Const 0) x => x
| Add x (Const 0) => x
| Mul (Const 0) x => Const 0
| Mul x (Const 0) => Const 0
| Mul (Const 1) x => x
| Mul x (Const 1) => x
| x => x

partial def simplify : Expression → Expression
| Add e₁ e₂ => simplify₁ (Add (simplify e₁) (simplify e₂))
| Mul e₁ e₂ => simplify₁ (Mul (simplify e₁) (simplify e₂))
| x => simplify₁ x

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

#eval let e := Add (Mul (Add (Mul (Const 0) (Var "x")) (Const 1)) (Const 3)) (Const 12) 
      simplify e

end Expression

-- (* ------------------------------------------------------------------------- *)
-- (* Lexical analysis.                                                         *)
-- (* ------------------------------------------------------------------------- *)

-- let matches s = let chars = explode s in fun c -> mem c chars;;
def matches s c :=
  let chars := explode s
  chars.elem c

def space := matches " \n\t\r"
def punctuation := matches "(){}[],"
def symbolic := matches "~‘!@#$%^&*-+=|\\:;<>.?/"
def numeric := matches "0123456789"
def alphanumeric := matches
"abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

def lexwhile (prop : String → Bool) : (inp : List String) → String × List String
| c :: cs => 
  if prop c then
    let ⟨tok, rest⟩ := lexwhile prop cs
    (c ++ tok, rest)
  else
    ("", c::cs)
| [] => ("", [])

partial def lex (inp : List String) : List String :=
  match (lexwhile space inp).snd with
  | [] => []
  | c :: cs => 
    let prop := 
      if alphanumeric c then 
        alphanumeric 
      else if symbolic c then
        symbolic
      else
        λ x => false
    let ⟨tokl, rest⟩ := lexwhile prop cs
    (c ++ tokl) :: lex rest

#eval explode "2*((var_1 + x') + 11)" |> lex
#eval explode "if (*p1-- == *p2++) then f() else g()" |> lex

-- (* ------------------------------------------------------------------------- *)
-- (* Parsing.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

namespace Expression

mutual 
partial def parseExpression (i : List String) : Optional (Expression × List String) := 
  match parseProduct i with
  | Result.Ok (e₁, "+"::i₁) => 
    parseExpression i₁ |>.map (λ p => (Expression.Add e₁ p.1, p.2))
  | x => x
partial def parseProduct (i : List String) : Optional (Expression × List String) := 
  match parseAtom i with
  | Result.Ok (e₁, "*"::i₁) =>
    parseProduct i₁ |>.map (λ p => (Expression.Mul e₁ p.1, p.2))
  | x => x
partial def parseAtom (i : List String) : Optional (Expression × List String) := 
  match i with
  | [] => Result.Err "Expected Expression at End of Input"
  | "("::i₁ => match parseExpression i₁ with
               | Result.Ok (e₂, ")"::i₂) => Result.Ok (e₂, i₂)
               | _ => Result.Err "Expected Closing Bracket"
  | tok::i₁ => if tok |> explode |>.all numeric then
    Result.Ok (Expression.Const tok.toInt!, i₁)
  else
    Result.Ok (Expression.Var tok, i₁)
end

end Expression


-- (* ------------------------------------------------------------------------- *)
-- (* Generic function to impose lexing and exhaustion checking on a parser.    *)
-- (* ------------------------------------------------------------------------- *)

def makeParser (pfn : List String → Optional (α × List β)) (s : String) : Optional α :=
  s |> explode |> lex |> pfn |>.andThen
  (λ ⟨expr, rest⟩ => if rest.isEmpty then Result.Ok expr else Result.Err "Unparsed Input")
  
  -- (λ Expr
  -- if rest.isEmpty then Result.Ok expr else Result.Err "Unparsed Input"
  -- )

-- (* ------------------------------------------------------------------------- *)
-- (* Our parser.                                                               *)
-- (* ------------------------------------------------------------------------- *)

def defaultParser := makeParser Expression.parseExpression

#eval defaultParser "x + 1"

-- (* ------------------------------------------------------------------------- *)
-- (* Demonstrate automatic installation.                                       *)
-- (* ------------------------------------------------------------------------- *)

-- Omitted

-- (* ------------------------------------------------------------------------- *)
-- (* Conservatively bracketing first attempt at printer.                       *)
-- (* ------------------------------------------------------------------------- *)

namespace Expression

def StringOfExp' : Expression → String
| Var s => s
| Const n => toString n
| Add e₁ e₂ => "(" ++ StringOfExp' e₁ ++ " + " ++ StringOfExp' e₂ ++ ")"
| Mul e₁ e₂ => "(" ++ StringOfExp' e₁ ++ " * " ++ StringOfExp' e₂ ++ ")"


-- (* ------------------------------------------------------------------------- *)
-- (* Examples.                                                                 *)
-- (* ------------------------------------------------------------------------- *)

-- #eval defaultParser "x + 3 * y" |> StringOfExp'

-- (* ------------------------------------------------------------------------- *)
-- (* Somewhat better attempt.                                                  *)
-- (* ------------------------------------------------------------------------- *)

def StringOfExp (pr : Nat) : Expression → String
| Var s => s
| Const n => toString n
| Add e₁ e₂ =>
  let s := StringOfExp 3 e₁ ++ " + " ++ StringOfExp 2 e₂
  if 2 < pr then
    "(" ++ s ++ ")"
  else
    s
| Mul e₁ e₂ =>
  let s := StringOfExp 5 e₁ ++ " * " ++ StringOfExp 4 e₂
  if 4 < pr then
    "(" ++ s ++ ")"
  else
    s

-- (* ------------------------------------------------------------------------- *)
-- (* Install it.                                                               *)
-- (* ------------------------------------------------------------------------- *)

-- Omitted

-- (* ------------------------------------------------------------------------- *)
-- (* Examples.                                                                 *)
-- (* ------------------------------------------------------------------------- *)

#eval defaultParser "x + 3 * y" |>.map <| StringOfExp 0
#eval defaultParser "x + (3 * y)" |>.map <| StringOfExp 0
#eval defaultParser "1 + 2 + 3" |>.map <| StringOfExp 0
#eval defaultParser "((1 + 2) + 3) + 4" |>.map <| StringOfExp 0

-- (* ------------------------------------------------------------------------- *)
-- (* Example shows the problem.                                                *)
-- (* ------------------------------------------------------------------------- *)

#eval defaultParser "(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) * (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)" |>.map <| StringOfExp 0

end Expression
