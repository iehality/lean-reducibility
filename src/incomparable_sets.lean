import reducibility computable_function

open encodable denumerable roption decidable

namespace t_reducible

namespace Kleene_Post

def extendable_ff (l : list bool) (n : ℕ) := λ x : ℕ, ∃ f : ℕ → bool, l ⊂ₘ f ∧ ⟦x⟧^f n = some ff
def extendable_tt (l : list bool) (n : ℕ) := λ x : ℕ, ∃ f : ℕ → bool, l ⊂ₘ f ∧ ⟦x⟧^f n = some tt

def extendable₀_le_0prime (l : list bool) (n): 
  extendable_ff l n ≤ₜ ∅′ :=
by sorry

noncomputable mutual def L₀, L₁
with L₀ : ℕ → list bool
| 0     := []
| (e+1) := 
  decidable.cases_on (classical.dec (extendable_ff (L₁ e) (L₀ e).length e))
    (λ _, L₀ e)
    (λ _, decidable.cases_on (classical.dec (extendable_tt (L₁ e) (L₀ e).length e))
      (λ _, tt :: L₀ e)
      (λ _, ff :: L₀ e))
with L₁ : ℕ → list bool
| 0     := []
| (e+1) := 
  decidable.cases_on (classical.dec (extendable_ff (L₀ e) (L₁ e).length e))
    (λ _, L₁ e)
    (λ _, decidable.cases_on (classical.dec (extendable_tt (L₀ e) (L₁ e).length e))
      (λ _, tt :: L₁ e)
      (λ _, ff :: L₁ e))

def I₀ : set ℕ := {n | ∃ s, (L₀ s).nth n = tt}  
def I₁ : set ℕ := {n | ∃ s, (L₁ s).nth n = tt}  

lemma inconparable01 : I₀ ≰ₜ I₁ :=
begin
  assume h : I₀ ≤ₜ I₁,
  have l0 : ↑(chr I₀) partrec_in ↑(chr I₁) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧^(chr I₁) = ↑(chr I₀) := rpartrec.rpartrec_univ_iff.mp l0,
  rcases this with ⟨e, he⟩,
  cases classical.dec (extendable_ff (L₁ e) (L₀ e).length e) with F F;
  cases classical.dec (extendable_tt (L₁ e) (L₀ e).length e) with T T,
  have : L₀ e = 

end

theorem Kleene_Post : ∃ (A B : set ℕ), (A ≤ₜ ∅′) ∧ (B ≤ₜ ∅′) ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end Kleene_Post

theorem Friedberg_Muchnik : ∃ (A B : set ℕ), re_pred A ∧ re_pred B ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end t_reducible