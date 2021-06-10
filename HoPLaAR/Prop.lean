/-
Copyright (c) 2003-2007, John Harrison
Copyright (c) 2021, Shing Tak Lam
(See "LICENSE" for details)
-/
import HoPLaAR.Formulas
import HoPLaAR.Intro
-- (* ========================================================================= *)
-- (* Basic stuff for propositional logic: datatype, parsing and printing.      *)
-- (* ========================================================================= *)

inductive prop
| P (name : String)
deriving Repr, BEq, Inhabited


def prop.name : prop → String
| P n => n

instance : LT prop :=
⟨λ s t => s.name < t.name⟩

instance : ToString prop := ⟨prop.name⟩

instance : DecidableRel (· < · : prop → prop → Prop) := 
  λ x y => String.decLt x.name y.name


-- (* ------------------------------------------------------------------------- *)
-- (* Parsing of propositional formulas.                                        *)
-- (* ------------------------------------------------------------------------- *)

def parsePropVar (vs : α) : List String → Optional (Formula prop × List String)
| p :: oinp => 
  if p != "(" then 
    Result.Ok (Formula.Atom (prop.P p), oinp)
  else
    Result.Err "parsePropVar"
| _ => Result.Err "parsePropVar"

def parsePropFormula := makeParser (parseFormula (λ _ _ => Result.Err "") parsePropVar [])

-- (* ------------------------------------------------------------------------- *)
-- (* Set this up as default for quotations.                                    *)
-- (* ------------------------------------------------------------------------- *)

-- Omitted

-- (* ------------------------------------------------------------------------- *)
-- (* Printer.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

def printPropVar (prec : Nat) (p : prop) := p.name

def printPropFormula := printFormula printPropVar

-- (* ------------------------------------------------------------------------- *)
-- (* Testing the parser and printer.                                           *)
-- (* ------------------------------------------------------------------------- *)

#eval let fm := "p ==> q <=> r /\\ s \\/ (t <=> ~ ~u /\\ v)"
  parsePropFormula fm |>.map printPropFormula

#eval let fm := "p ==> q <=> r /\\ s \\/ (t <=> ~ ~u /\\ v)"
  parsePropFormula fm |>.map (λ p => printPropFormula (Formula.And p p))

#eval let fm := "p ==> q <=> r /\\ s \\/ (t <=> ~ ~u /\\ v)"
  parsePropFormula fm |>.map (λ p => printPropFormula (Formula.And (Formula.Or p p) p))

-- (* ------------------------------------------------------------------------- *)
-- (* Interpretation of formulas.                                               *)
-- (* ------------------------------------------------------------------------- *)

def eval : Formula α → (α → Bool) → Optional Bool
| Formula.False, _ => Result.Ok false
| Formula.True, _ => Result.Ok true
| Formula.Atom x, v => Result.Ok <| v x
| Formula.Not p, v => eval p v |>.map not
| Formula.And p q, v => eval p v |>.zip (eval q v) and
| Formula.Or p q, v => eval p v |>.zip (eval q v) or
| Formula.Imp p q, v => eval p v |>.map not |>.zip (eval q v) or
| Formula.Iff p q, v => eval p v |>.zip (eval q v) (·==·)
| _, _ => Result.Err "Invalid Propositional Logic Formula"

-- (* ------------------------------------------------------------------------- *)
-- (* Example of use.                                                           *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "p /\\ q ==> q /\\ r" |>.andThen (eval · fun
                                                              | prop.P "p" => true
                                                              | prop.P "q" => false
                                                              | prop.P "r" => true
                                                              | _ => false)

#eval parsePropFormula "p /\\ q ==> q /\\ r" |>.andThen (eval · fun
                                                              | prop.P "p" => true
                                                              | prop.P "q" => true
                                                              | prop.P "r" => false
                                                              | _ => false)

-- (* ------------------------------------------------------------------------- *)
-- (* Return the set of propositional variables in a formula.                   *)
-- (* ------------------------------------------------------------------------- *)

def atoms [LT α] [BEq α] [DecidableRel (· < · : α → α → Prop)] [Inhabited α]
  (fm : Formula α) : List α := atomUnion (fun a => [a]) fm

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "p /\\ q \\/ s ==> ~p \\/ (r <=> s)" |>.map atoms

-- (* ------------------------------------------------------------------------- *)
-- (* Code to print out truth tables.                                           *)
-- (* ------------------------------------------------------------------------- *)

def onAllValuations [BEq α] [Append β] (subfn : (α → Bool) → β) (v : α → Bool) : List α → β
| [] => subfn v
| p :: ps => 
  let v' t q := if q == p then t else v q
  onAllValuations subfn (v' false) ps ++ onAllValuations subfn (v' true) ps

def printTruthTable (fm : Formula prop) : Optional String :=
  let ats := atoms fm
  let width := ats.foldr (Nat.max ∘ String.length ∘ prop.name) 5 + 1
  let fixw s := String.pushn s ' ' (width - s.length)
  let truthString (p : Bool) := fixw (if p then "true" else "false")
  let mkRow (v : prop → Bool) :=
    let lis := ats.map (λ x => truthString (v x))
    let ans := eval fm v
    ans.map <| λ s => lis.foldr (·++·) ("| " ++ truthString s) ++ "\n"
  let sep := "".pushn '-' (width * ats.length + 9)
  let top := ats.foldr (λ s t => fixw s.name ++ t) "| formula"
  let table := onAllValuations mkRow (λ x => false) ats
  table.map <| λ r => top ++ "\n" ++ sep ++ r ++ sep
-- let print_truthtable fm =
--   let ats = atoms fm in
--   let width = itlist (max ** String.length ** pname) ats 5 + 1 in
--   let fixw s = s^String.make(width - String.length s) ' ' in
--   let truthstring p = fixw (if p then "true" else "false") in
--   let mk_row v =
--      let lis = map (fun x -> truthstring(v x)) ats
--      and ans = truthstring(eval fm v) in
--      print_string(itlist (^) lis ("| "^ans)); print_newline(); true in
--   let separator = String.make (width * length ats + 9) '-' in
--   print_string(itlist (fun s t -> fixw(pname s) ^ t) ats "| formula");
--   print_newline(); print_string separator; print_newline();
--   let _ = onallvaluations mk_row (fun x -> false) ats in
--   print_string separator; print_newline()

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

-- Lean doesn't do multiline strings :|
#eval parsePropFormula "p /\\ q ==> q /\\ r" |>.andThen printTruthTable |>.unwrap!

-- (* ------------------------------------------------------------------------- *)
-- (* Additional examples illustrating formula classes.                         *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "((p ==> q) ==> p) ==> p" |>.andThen printTruthTable |>.unwrap!

#eval parsePropFormula "p /\\ ~p" |>.andThen printTruthTable |>.unwrap!

-- (* ------------------------------------------------------------------------- *)
-- (* Recognizing tautologies.                                                  *)
-- (* ------------------------------------------------------------------------- *)

section

local instance : Append Bool := ⟨and⟩

def tautology (fm : Formula prop) :=
  onAllValuations (eval fm) (λ s => false) (atoms fm)

end

-- (* ------------------------------------------------------------------------- *)
-- (* Examples.                                                                 *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "p \\/ ~p" |>.andThen tautology

#eval parsePropFormula "p \\/ q ==> p" |>.andThen tautology

#eval parsePropFormula "p \\/ q ==> q \\/ (p <=> q)" |>.andThen tautology

#eval parsePropFormula "(p \\/ q) /\\ ~(p /\\ q) ==> (~p <=> q)" |>.andThen tautology

-- (* ------------------------------------------------------------------------- *)
-- (* Related concepts.                                                         *)
-- (* ------------------------------------------------------------------------- *)

def unsatisfiable (f : Formula prop) := tautology (Formula.Not f)

def satisfiable (f : Formula prop) := unsatisfiable f |>.map not

-- (* ------------------------------------------------------------------------- *)
-- (* Substitution operation.                                                   *)
-- (* ------------------------------------------------------------------------- *)

-- let psubst subfn = onatoms (fun p -> tryapplyd subfn p (Atom p))

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

-- START_INTERACTIVE
-- psubst (P"p" |=> "p /\\ q") "p /\\ q /\\ p /\\ q"
-- END_INTERACTIVE

-- (* ------------------------------------------------------------------------- *)
-- (* Surprising tautologies including Dijkstra's "Golden rule".                *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "(p ==> q) \\/ (q ==> p)" |>.andThen tautology

#eval parsePropFormula "p \\/ (q <=> r) <=> (p \\/ q <=> p \\/ r)" |>.andThen tautology

#eval parsePropFormula "p /\\ q <=> ((p <=> q) <=> p \\/ q)" |>.andThen tautology

#eval parsePropFormula "(p ==> q) <=> (~q ==> ~p)" |>.andThen tautology

#eval parsePropFormula "(p ==> ~q) <=> (q ==> ~p)" |>.andThen tautology

#eval parsePropFormula "(p ==> q) <=> (q ==> p)" |>.andThen tautology

-- (* ------------------------------------------------------------------------- *)
-- (* Some logical equivalences allowing elimination of connectives.            *)
-- (* ------------------------------------------------------------------------- *)

#eval ["true <=> false ==> false",
  "~p <=> p ==> false",
  "p /\\ q <=> (p ==> q ==> false) ==> false",
  "p \\/ q <=> (p ==> false) ==> q",
  "(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false"]
  |>.map ((Result.andThen · tautology) ∘ parsePropFormula)
  |>.collect

-- (* ------------------------------------------------------------------------- *)
-- (* Dualization.                                                              *)
-- (* ------------------------------------------------------------------------- *)

def Formula.dual : Formula α → Optional (Formula α)
| False => Result.Ok True
| True => Result.Ok False
| Atom p => Result.Ok (Atom p)
| Not p => p.dual.map Not
| And p q => q.dual.zip p.dual Or
| Or p q => q.dual.zip p.dual And
| _ => Result.Err "Formula involves connectives ==>, <=> or quantifiers"

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "p \\/ ~p" |>.andThen Formula.dual

-- (* ------------------------------------------------------------------------- *)
-- (* Routine simplification.                                                   *)
-- (* ------------------------------------------------------------------------- *)


def psimplify₁ : Formula α → Formula α
| Formula.Not Formula.False => Formula.True
| Formula.Not Formula.True => Formula.False
| Formula.Not (Formula.Not p) => p
| Formula.And _ Formula.False => Formula.False
| Formula.And Formula.False _ => Formula.False
| Formula.And p Formula.True => p
| Formula.And Formula.True p => p
| Formula.Or p Formula.False => p
| Formula.Or Formula.False p => p
| Formula.Or _ Formula.True => Formula.True
| Formula.Or Formula.True _ => Formula.True
| Formula.Imp Formula.False p => Formula.True
| Formula.Imp p Formula.True => Formula.True
| Formula.Imp Formula.True p => p
| Formula.Imp p Formula.False => Formula.Not p
| Formula.Iff p Formula.True => p
| Formula.Iff Formula.True p => p
| f => f

def psimplify : Formula α → Formula α
| Formula.Not p => psimplify₁ (Formula.Not (psimplify p))
| Formula.And p q => psimplify₁ (Formula.And (psimplify p) (psimplify q))
| Formula.Or p q => psimplify₁ (Formula.Or (psimplify p) (psimplify q))
| Formula.Iff p q => psimplify₁ (Formula.Iff (psimplify p) (psimplify q))
| Formula.Imp p q => psimplify₁ (Formula.Imp (psimplify p) (psimplify q))
| f => f

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

-- START_INTERACTIVE
#eval parsePropFormula "(true ==> (x <=> false)) ==> ~(y \\/ false /\\ z)" 
  |>.map psimplify |>.map printPropFormula

#eval parsePropFormula "((x ==> y) ==> true) \\/ ~false"
  |>.map psimplify |>.map printPropFormula

-- (* ------------------------------------------------------------------------- *)
-- (* Some operations on literals.                                              *)
-- (* ------------------------------------------------------------------------- *)

def negative : Formula α → Bool  := fun | (Formula.Not p) => true | _ => false


def positive (lit : Formula α) := !negative lit

def negate : Formula α → Formula α := fun | (Formula.Not p) => p | p => Formula.Not p

-- (* ------------------------------------------------------------------------- *)
-- (* Negation normal form.                                                     *)
-- (* ------------------------------------------------------------------------- *)

partial def nnf' : Formula α → Formula α
| Formula.And p q => Formula.And (nnf' p) (nnf' q)
| Formula.Or p q => Formula.Or (nnf' p) (nnf' q)
| Formula.Imp p q => Formula.Or (nnf' (Formula.Not p)) (nnf' q)
| Formula.Iff p q => Formula.Or (Formula.And (nnf' p) (nnf' q)) 
  (Formula.And (nnf' (Formula.Not p)) (nnf' (Formula.Not q)))
| Formula.Not (Formula.Not p) => nnf' p
| Formula.Not (Formula.And p q) => Formula.Or (nnf' (Formula.Not p)) (nnf' (Formula.Not q))
| Formula.Not (Formula.Or p q) => Formula.And (nnf' (Formula.Not p)) (nnf' (Formula.Not q))
| Formula.Not (Formula.Imp p q) => Formula.And (nnf' p) (nnf' (Formula.Not q))
| Formula.Not (Formula.Iff p q) => Formula.Or (Formula.And (nnf' p) (nnf' (Formula.Not q))) 
  (Formula.And (nnf' (Formula.Not p)) (nnf' q))
| f => f

-- (* ------------------------------------------------------------------------- *)
-- (* Roll in simplification.                                                   *)
-- (* ------------------------------------------------------------------------- *)

partial def nnf (fm : Formula α) : Formula α := nnf' (psimplify fm)

-- (* ------------------------------------------------------------------------- *)
-- (* Example of NNF function in action.                                        *)
-- (* ------------------------------------------------------------------------- *)

namespace hidden
private def t := parsePropFormula "(p <=> q) <=> ~(r ==> s)"

#eval t.map nnf

#eval t.andThen (λ x => tautology (Formula.Iff x (nnf x)))
end hidden

-- END_INTERACTIVE

-- (* ------------------------------------------------------------------------- *)
-- (* Simple negation-pushing when we don't care to distinguish occurrences.    *)
-- (* ------------------------------------------------------------------------- *)

partial def nenf' : Formula α → Formula α
| Formula.Not (Formula.Not p) => nenf' p
| Formula.Not (Formula.And p q) => Formula.Or (nenf' (Formula.Not p)) (nenf' (Formula.Not q))
| Formula.Not (Formula.Or p q) => Formula.And (nenf' (Formula.Not p)) (nenf' (Formula.Not q))
| Formula.Not (Formula.Imp p q) => Formula.And (nenf' p) (nenf' (Formula.Not q))
| Formula.Not (Formula.Iff p q) => Formula.Iff (nenf' p) (nenf' (Formula.Not q))
| Formula.And p q => Formula.And (nenf' p) (nenf' q)
| Formula.Or p q => Formula.Or (nenf' p) (nenf' q)
| Formula.Imp p q => Formula.Or (nenf' (Formula.Not p)) (nenf' q)
| Formula.Iff p q => Formula.Iff (nenf' p) (nenf' q)
| fm => fm

partial def nenf (fm : Formula α) : Formula α := nenf (psimplify fm)

-- (* ------------------------------------------------------------------------- *)
-- (* Some tautologies remarked on.                                             *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "(p ==> p') /\\ (q ==> q') ==> (p /\\ q ==> p' /\\ q')" |>.andThen tautology
#eval parsePropFormula "(p ==> p') /\\ (q ==> q') ==> (p \\/ q ==> p' \\/ q')" |>.andThen tautology

-- (* ------------------------------------------------------------------------- *)
-- (* Disjunctive normal form (DNF) via truth tables.                           *)
-- (* ------------------------------------------------------------------------- *)

def listConj [BEq α] (l : List (Formula α)) := if l == [] then Formula.True else l.reducer Formula.And

def listDisj [BEq α] (l : List (Formula α)) := if l == [] then Formula.False else l.reducer Formula.Or

def mkLits [BEq α] (pvs : List (Formula α)) (v : α → Bool) : Formula α :=
  listConj (pvs.map (λ p => if eval p v |>.unwrapD false then p else Formula.Not p))

def allSatValuations [BEq α] (subfn : (α → Bool) → Optional Bool) (v : α → Bool) (pvs : List α) : Optional (List (α → Bool)) :=
  match pvs with
  | [] => if subfn v |>.unwrapD false then Result.Ok [v] else Result.Ok []
  | p :: ps => 
    let v' t q := if q == p then t else v q
    allSatValuations subfn (v' false) ps
    ++ allSatValuations subfn (v' true) ps

def dnf [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] [Inhabited α] (fm : Formula α) : Optional (Formula α) :=
  let pvs := atoms fm
  let satVals := allSatValuations (eval fm) (λ _ => false) pvs
  satVals.map <| λ l => l.map (mkLits (List.map (λ p => Formula.Atom p) pvs)) |> listDisj

-- (* ------------------------------------------------------------------------- *)
-- (* Examples.                                                                 *)
-- (* ------------------------------------------------------------------------- *)

namespace hidden
private def fm := parsePropFormula "(p \\/ q /\\ r) /\\ (~p \\/ ~r)"

#eval fm.andThen dnf |>.map printPropFormula

#eval fm.andThen printTruthTable

#eval parsePropFormula "p /\\ q /\\ r /\\ s /\\ t /\\ u \\/ u /\\ v" |>.andThen dnf |>.map printPropFormula
end hidden

-- (* ------------------------------------------------------------------------- *)
-- (* DNF via distribution.                                                     *)
-- (* ------------------------------------------------------------------------- *)

partial def distrib : Formula α → Formula α
| Formula.And p (Formula.Or q r) => Formula.Or (distrib (Formula.And p q)) (distrib (Formula.And p r))
| Formula.And (Formula.Or p q) r => Formula.Or (distrib (Formula.And p r)) (distrib (Formula.And q r))
| f => f

def rawDnf : Formula α → Formula α
| Formula.And p q => distrib (Formula.And (rawDnf p) (rawDnf q))
| Formula.Or p q => Formula.Or (rawDnf p) (rawDnf q)
| f => f

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "(p \\/ q /\\ r) /\\ (~p \\/ ~r)" |>.map rawDnf |>.map printPropFormula

-- (* ------------------------------------------------------------------------- *)
-- (* A version using a list representation.                                    *)
-- (* ------------------------------------------------------------------------- *)

def distrib' [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] [Inhabited α] 
  (s1 s2 : List (List α)) := setify (allPairs union s1 s2)

def pureDnf [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] [Inhabited α] [ToString α]
  : Formula α → List (List (Formula α))
| Formula.And p q => distrib' (pureDnf p) (pureDnf q)
| Formula.Or p q => union (pureDnf p) (pureDnf q)
| f => [[f]]

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "(p \\/ q /\\ r) /\\ (~p \\/ ~r)" |>.map pureDnf

-- (* ------------------------------------------------------------------------- *)
-- (* Filtering out trivial disjuncts (in this guise, contradictory).           *)
-- (* ------------------------------------------------------------------------- *)

def trivialDisj [BEq α] [ToString α] (lits : List (Formula α)) : Bool :=
  let (pos, neg) := lits.partition positive
  intersect pos (image negate neg) |>.isEmpty |> not

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

#eval parsePropFormula "(p \\/ q /\\ r) /\\ (~p \\/ ~r)" |>.map pureDnf |>.map <| List.filter (non trivialDisj)

-- (* ------------------------------------------------------------------------- *)
-- (* With subsumption checking, done very naively (quadratic).                 *)
-- (* ------------------------------------------------------------------------- *)

-- let simpdnf fm =
--   if fm = False then [] else if fm = True then [[]] else
--   let djs = filter (non trivial) (purednf(nnf fm)) in
--   filter (fun d -> not(exists (fun d' -> psubset d' d) djs)) djs

-- (* ------------------------------------------------------------------------- *)
-- (* Mapping back to a formula.                                                *)
-- (* ------------------------------------------------------------------------- *)

-- let dnf fm = list_disj(map list_conj (simpdnf fm))

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

-- START_INTERACTIVE
-- let fm = "(p \\/ q /\\ r) /\\ (~p \\/ ~r)"
-- dnf fm
-- tautology(Iff(fm,dnf fm))
-- END_INTERACTIVE

-- (* ------------------------------------------------------------------------- *)
-- (* Conjunctive normal form (CNF) by essentially the same code.               *)
-- (* ------------------------------------------------------------------------- *)

-- let purecnf fm = image (image negate) (purednf(nnf(Not fm)))

-- let simpcnf fm =
--   if fm = False then [[]] else if fm = True then [] else
--   let cjs = filter (non trivial) (purecnf fm) in
--   filter (fun c -> not(exists (fun c' -> psubset c' c) cjs)) cjs

-- let cnf fm = list_conj(map list_disj (simpcnf fm))

-- (* ------------------------------------------------------------------------- *)
-- (* Example.                                                                  *)
-- (* ------------------------------------------------------------------------- *)

-- START_INTERACTIVE
-- let fm = "(p \\/ q /\\ r) /\\ (~p \\/ ~r)"
-- cnf fm
-- tautology(Iff(fm,cnf fm))
-- END_INTERACTIVE
