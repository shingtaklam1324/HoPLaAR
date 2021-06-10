inductive Result (α : Type u) (β : Type v)
| Ok (a : α)
| Err (b : β)
deriving Repr, BEq

abbrev Optional (α : Type u) := Result α String

namespace Result

instance [Inhabited α] : Inhabited (Result α β) := ⟨Ok arbitrary⟩
instance [Inhabited β] : Inhabited (Result α β) := ⟨Err arbitrary⟩

def map : Result α β → (α → γ) → Result γ β
| Ok x, f => Ok (f x)
| Err e, f => Err e

def bind₂ : Result α β → (α → Result γ δ) → (β → Result γ δ) → Result γ δ
| Ok x, f, g => f x
| Err x, f, g => g x

def andThen (r : Result α β) (f : α → Result γ β) : Result γ β := r.bind₂ f Result.Err
def orElse (r : Result α β) (f : β → Result α γ) : Result α γ := r.bind₂ Result.Ok f

def zip : Result α β → Result γ β → (α → γ → δ) → Result δ β
| Ok x, Ok y, f => Ok <| f x y
| Err e, _, f => Err e
| _, Err e, f => Err e

instance [Append α] [Append β] : Append (Result α β) :=
  ⟨fun
   | Ok x, Ok y => Ok (x ++ y)
   | Ok x, Err e => Err e
   | Err e, Ok x => Err e
   | Err e, Err f => Err (e ++ f)⟩

def unwrap! [Inhabited α] : Result α β → α
| Ok x => x
| Err _ => panic! "Unwrapped an Err"

def unwrapD : Result α β → α → α
| Ok x, _ => x
| Err _, y => y

end Result

def Option.withErr : Option α → β → Result α β
| some x, _ => Result.Ok x
| none, e => Result.Err e

def List.collect : List (Result α β) → Result (List α) β
| [] => Result.Ok []
| Result.Ok a :: t => t.collect.map (a :: ·)
| Result.Err b :: t => Result.Err b
