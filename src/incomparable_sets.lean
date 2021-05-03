import reducibility computable_function

open encodable denumerable roption decidable

namespace Kleene_Post

def extendable (l : list ℕ) (n : ℕ) := {x : ℕ | ∃ f, l ⊂ₘ f ∧ (⟦x⟧^f n : roption bool).dom}

def extendable_le_0prime (l : list ℕ) (n): 
  extendable l n ≤ₜ ∅′ :=
by sorry

mutual def I₀, I₁

with I₀ : ℕ → list ℕ
| 0     := []
| (e+1) := if p : e ∈ extendable (I₁ e) (I₀ e).length then 

with I₁ : ℕ → list ℕ
| 0     := []
| (n+1) := ∃ q, sigma0_hie n q ∧ ∀ a, p a ↔ (∀ b, q (a.mkpair b))

def incomparable_sets : ℕ → list ℕ × list ℕ
| 0     := ([], [])
| (n+1) := 

theorem Kleene_Post : ∃ (A B : set ℕ), (A ≤ₜ ∅′) ∧ (B ≤ₜ ∅′) ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end Kleene_Post


theorem Kleene_Post0 : ∃ (A : set ℕ), ((∅ : set ℕ) <ₜ A) ∧ (A <ₜ ∅′) :=
by sorry

theorem Friedberg_Muchnik : ∃ (A B : set ℕ), re_pred A ∧ re_pred B ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry