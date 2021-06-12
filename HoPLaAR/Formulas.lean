/-
Copyright (c) 2003-2007, John Harrison
Copyright (c) 2021, Shing Tak Lam
(See "LICENSE" for details)
-/
import HoPLaAR.Aux.Result
import HoPLaAR.Lib

inductive Formula (α : Type _)
| False
| True
| Atom (a : α)
| Not (f : Formula α)
| And (f₁ f₂ : Formula α)
| Or (f₁ f₂ : Formula α)
| Imp (f₁ f₂ : Formula α)
| Iff (f₁ f₂ : Formula α)
| Forall (s : String) (f : Formula α)
| Exists (s : String) (f : Formula α)
deriving Inhabited, Repr, BEq, DecidableEq

/--
Only defined so that we can use Lex order for an ordering, do *not* use in general
-/
def Formula.toString [ToString α] : Formula α → String
| False => "False"
| True => "True"
| Atom p => s! "Atom {p}"
| Not f => s! "Not ({f.toString})"
| And f g => s! "And ({f.toString}) ({g.toString})"
| Or f g => s! "Or ({f.toString}) ({g.toString})"
| Imp f g => s! "Imp ({f.toString}) ({g.toString})"
| Iff f g => s! "Iff ({f.toString}) ({g.toString})"
| Forall f g => s! "Forall ({f}) ({g.toString})"
| Exists f g => s! "Exists ({f}) ({g.toString})"

def Formula.lt [ToString α] (f₁ f₂ : Formula α) : Prop := f₁.toString < f₂.toString

instance [ToString α] : LT (Formula α) := ⟨Formula.lt⟩

instance [ToString α] : DecidableRel (· < · : Formula α → Formula α → Prop) :=
λ f g => String.decLt _ _

-- (* ------------------------------------------------------------------------- *)
-- (* General parsing of iterated infixes.                                      *)
-- (* ------------------------------------------------------------------------- *)

partial def parseGInfix [BEq α]
  (opsym : α) (opupdate : (β → γ) → β → β → γ) (sof : β → γ) 
  (subparser : List α → Optional (β × List α)) (inp : List α) : 
  Optional (γ × List α) :=
  subparser inp |>.andThen <| λ ⟨e₁, inp₁⟩ =>
  if !inp₁.isEmpty && inp₁.head? == some opsym then
    inp₁.tail?.withErr "Expected expression after infix symbol" |>.andThen 
      <| parseGInfix opsym opupdate (opupdate sof e₁) subparser
  else
    Result.Ok (sof e₁, inp₁)

def parseLeftInfix [BEq α] (opsym : α) (opcon : β → β → β) : 
  (List α → Optional (β × List α)) → List α → Optional (β × List α) :=
  parseGInfix opsym (λ f e₁ e₂ => opcon (f e₁) e₂) id

def parseRightInfix [BEq α] (opsym : α) (opcon : β → β → β) : 
  (List α → Optional (β × List α)) → List α → Optional (β × List α) :=
  parseGInfix opsym (λ f e₁ e₂ => f (opcon e₁ e₂)) id

def parseList [BEq α] (opsym : α) : (List α → Optional (β × List α)) → 
  List α → Optional (List β × List α) := 
parseGInfix opsym (λ f e₁ e₂ => (f e₁) ++ [e₂]) (λ x => [x])

-- (* ------------------------------------------------------------------------- *)
-- (* Other general parsing combinators.                                        *)
-- (* ------------------------------------------------------------------------- *)

def papply (f : α → β) : α × γ → β × γ
| (a, b) => (f a, b)

def nextIn {α} [Inhabited α] [BEq α] (inp : List α) (tok) :=
  !inp.isEmpty && inp.head? == some tok

def parseBracketed [Inhabited β] [Inhabited γ] [BEq γ]
  (subparser : α → Optional (β × List γ)) (cbra : γ) (inp : α) : Optional (β × List γ) :=
  -- let (ast, rest) := 
  subparser inp |>.andThen <| λ ⟨ast, rest⟩ =>
  if nextIn rest cbra then
    rest.tail?.withErr "parseBracketed" |>.map (ast, ·)
  else
    Result.Err ""
      
-- (* ------------------------------------------------------------------------- *)
-- (* Parsing of formulas, parametrized by atom parser "pfn".                   *)
-- (* ------------------------------------------------------------------------- *)

mutual

partial def parseAtomicFormula (ifn afn : List String → List String → Optional (Formula α × List String)) 
  (vs : List String) : List String → Optional (Formula α × List String)
| [] => Result.Err "Formula Expected"
| "false" :: rest => Result.Ok (Formula.False, rest)
| "true" :: rest => Result.Ok (Formula.True, rest)
| "(" :: rest =>
  ifn vs rest |>.orElse λ _ => parseBracketed (parseFormula ifn afn vs) ")" rest
| "~" :: rest => 
  parseAtomicFormula ifn afn vs rest |>.map <| papply Formula.Not
| "forall" :: x :: rest =>
  parseQuant ifn afn (x :: vs) Formula.Forall x rest
| "exists" :: x :: rest =>
  parseQuant ifn afn (x :: vs) Formula.Exists x rest
| inp => afn vs inp

partial def parseQuant (ifn afn : List String → List String → Optional (Formula α × List String)) 
  (vs : List String) (qcon : String → Formula α → Formula α) (x : String) : 
List String → Optional (Formula α × List String)
| [] => Result.Err "Formula Expected"
| y :: rest =>
  if y == "." then
    parseFormula ifn afn vs rest
  else
    parseQuant ifn afn (y :: vs) qcon y rest |>.map <| papply <| qcon x

partial def parseFormula (ifn afn : List String → List String → Optional (Formula α × List String))
  (vs inp : List String) : Optional (Formula α × List String) := 
  (parseRightInfix "<=>" Formula.Iff 
    <| parseRightInfix "==>" Formula.Imp
    <| parseRightInfix "\\/" Formula.Or
    <| parseRightInfix "/\\" Formula.And
    <| parseAtomicFormula ifn afn vs) inp

end

-- (* ------------------------------------------------------------------------- *)
-- (* Printing of formulas, parametrized by atom printer.                       *)
-- (* ------------------------------------------------------------------------- *)

def bracket (p : Bool) (f : β → γ → String) (x : β) (y : γ) :=
  if p then
    "(" ++ f x y ++ ")"
  else
    f x y

partial def stripQuant : Formula α → List String × Formula α
| Formula.Forall x yp@(Formula.Forall y p) => 
  let (xs, q) := stripQuant yp
  (x :: xs, q)
| Formula.Exists x yp@(Formula.Exists y p) => 
  let (xs, q) := stripQuant yp
  (x :: xs, q)
| Formula.Forall x p => ([x], p)
| Formula.Exists x p => ([x], p)
| f => ([], f)

mutual
partial def printFormula' (pfn : Nat → α → String) (pr : Nat) : Formula α → String
| Formula.False => "false"
| Formula.True => "true"
| Formula.Atom p => pfn pr p
| Formula.Not p => bracket (pr > 10) (printPrefix pfn 10) "~" p
| Formula.And p q => bracket (pr > 8) (printInfix pfn 8 "/\\") p q
| Formula.Or p q => bracket (pr > 6) (printInfix pfn 6 "\\/") p q
| Formula.Imp p q => bracket (pr > 4) (printInfix pfn 4 "==>") p q
| Formula.Iff p q => bracket (pr > 2) (printInfix pfn 2 "<=>") p q
| f@(Formula.Forall x p) => 
  let ⟨bvs, bod⟩ := stripQuant f
  bracket (pr > 0) (printQnt pfn "forall") bvs bod
| f@(Formula.Exists x p) => 
  let ⟨bvs, bod⟩ := stripQuant f
  bracket (pr > 0) (printQnt pfn "forall") bvs bod

partial def printQnt (pfn : Nat → α → String) (qname : String) (bvs : List String) (bod : Formula α) : String := 
  qname ++ String.intercalate " " bvs ++ ". " ++ printFormula' pfn 0 bod

partial def printPrefix (pfn : Nat → α → String) (newpr : Nat) (sym : String) (p : Formula α) := 
  sym ++ printFormula' pfn (newpr + 1) p

partial def printInfix (pfn : Nat → α → String) (newpr : Nat) (sym : String) (p q : Formula α) :=
  printFormula' pfn (newpr + 1) p ++ " " ++ sym ++ " " ++ printFormula' pfn newpr q
end

def printFormula (pfn : Nat → α → String) : Formula α → String :=
  printFormula' pfn 0

-- let print_qformula pfn fm =
--   open_box 0; print_string "<<";
--   open_box 0; print_formula pfn fm; close_box();
--   print_string ">>"; close_box();;

-- (* ------------------------------------------------------------------------- *)
-- (* OCaml won't let us use the constructors.                                  *)
-- (* ------------------------------------------------------------------------- *)

-- let mk_and p q = And(p,q) and mk_or p q = Or(p,q)
-- and mk_imp p q = Imp(p,q) and mk_iff p q = Iff(p,q)
-- and mk_forall x p = Forall(x,p) and mk_exists x p = Exists(x,p);;

-- (* ------------------------------------------------------------------------- *)
-- (* Destructors.                                                              *)
-- (* ------------------------------------------------------------------------- *)

-- let dest_iff fm =
--   match fm with Iff(p,q) -> (p,q) | _ -> failwith "dest_iff";;

-- let dest_and fm =
--   match fm with And(p,q) -> (p,q) | _ -> failwith "dest_and";;

-- let rec conjuncts fm =
--   match fm with And(p,q) -> conjuncts p @ conjuncts q | _ -> [fm];;

-- let dest_or fm =
--   match fm with Or(p,q) -> (p,q) | _ -> failwith "dest_or";;

-- let rec disjuncts fm =
--   match fm with Or(p,q) -> disjuncts p @ disjuncts q | _ -> [fm];;

-- let dest_imp fm =
--   match fm with Imp(p,q) -> (p,q) | _ -> failwith "dest_imp";;

-- let antecedent fm = fst(dest_imp fm);;
-- let consequent fm = snd(dest_imp fm);;

-- (* ------------------------------------------------------------------------- *)
-- (* Apply a function to the atoms, otherwise keeping structure.               *)
-- (* ------------------------------------------------------------------------- *)

def onAtoms (f : α → Formula α) : Formula α → Formula α
| Formula.Atom a => f a
| Formula.Not p => Formula.Not (onAtoms f p)
| Formula.And p q => Formula.And (onAtoms f p) (onAtoms f q)
| Formula.Or p q => Formula.Or (onAtoms f p) (onAtoms f q)
| Formula.Imp p q => Formula.Imp (onAtoms f p) (onAtoms f q)
| Formula.Iff p q => Formula.Iff (onAtoms f p) (onAtoms f q)
| Formula.Forall x p => Formula.Forall x (onAtoms f p)
| Formula.Exists x p => Formula.Exists x (onAtoms f p)
| fm => fm

-- (* ------------------------------------------------------------------------- *)
-- (* Formula analog of list iterator "itlist".                                 *)
-- (* ------------------------------------------------------------------------- *)

def overatoms (f : α → β → β) : Formula α → β → β
| Formula.Atom a, b => f a b
| Formula.Not p, b => overatoms f p b
| Formula.And p q, b => overatoms f p (overatoms f q b)
| Formula.Or p q, b => overatoms f p (overatoms f q b)
| Formula.Imp p q, b => overatoms f p (overatoms f q b)
| Formula.Iff p q, b => overatoms f p (overatoms f q b)
| Formula.Forall x p, b => overatoms f p b
| Formula.Exists x p, b => overatoms f p b
| _, b => b

-- (* ------------------------------------------------------------------------- *)
-- (* Special case of a union of the results of a function over the atoms.      *)
-- (* ------------------------------------------------------------------------- *)

-- let atom_union f fm = setify (overatoms (fun h t -> f(h)@t) fm []);;
def atomUnion [Inhabited β] [LT β] [BEq β] [DecidableRel (· < · : β → β → Prop)] 
  (f : α → List β) (fm : Formula α) : List β :=
  setify <| overatoms (λ h t => f h ++ t) fm []
