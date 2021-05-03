import reducibility computable_function

open encodable denumerable roption decidable

namespace Kleene_Post

def extendable_ff (l : list ℕ) (n : ℕ) := λ x : ℕ, ∃ f, l ⊂ₘ f ∧ ⟦x⟧^f n = some ff
def extendable_tt (l : list ℕ) (n : ℕ) := λ x : ℕ, ∃ f, l ⊂ₘ f ∧ ⟦x⟧^f n = some tt

def extendable₀_le_0prime (l : list ℕ) (n): 
  extendable_ff l n ≤ₜ ∅′ :=
by sorry

noncomputable mutual def L₀, L₁
with L₀ : ℕ → list ℕ
| 0     := []
| (e+1) := 
  decidable.cases_on (classical.dec (extendable_ff (L₁ e) (L₀ e).length e))
    (λ _, L₀ e)
    (λ _, decidable.cases_on (classical.dec (extendable_tt (L₁ e) (L₀ e).length e))
      (λ _, (1 :: L₀ e))
      (λ _, (0 :: L₀ e)))
with L₁ : ℕ → list ℕ
| 0     := []
| (e+1) := 
  decidable.cases_on (classical.dec (extendable_ff (L₀ e) (L₁ e).length e))
    (λ _, L₁ e)
    (λ _, decidable.cases_on (classical.dec (extendable_tt (L₀ e) (L₁ e).length e))
      (λ _, (1 :: L₁ e))
      (λ _, (0 :: L₁ e)))

def I₀ : set ℕ := {n | ∃ s, n ∈ L₀ s}  
def I₁ : set ℕ := {n | ∃ s, n ∈ L₁ s}  

def incomparable_sets : ℕ → list ℕ × list ℕ
| 0     := ([], [])
| (n+1) := 

theorem Kleene_Post : ∃ (A B : set ℕ), (A ≤ₜ ∅′) ∧ (B ≤ₜ ∅′) ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end Kleene_Post

theorem Friedberg_Muchnik : ∃ (A B : set ℕ), re_pred A ∧ re_pred B ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry