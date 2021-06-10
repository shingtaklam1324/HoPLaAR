class Bifunctor (b : Type u → Type v → Type w) where
  bimap : {α β γ δ : Type _} → (α → β) → (γ → δ) → (b α β → b γ δ)
