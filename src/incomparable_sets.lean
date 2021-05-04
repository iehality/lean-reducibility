import reducibility computable_function

open encodable denumerable roption decidable

namespace t_reducible

namespace Kleene_Post

def extendable (l₀ l : list bool) (n e : ℕ) := (⟦e⟧^((l₀ ++ l).nth) n : roption bool).dom
def extendable_ff (l₀ l : list bool) (n e : ℕ) := ⟦e⟧^((l₀ ++ l).nth) n = some ff
def extendable_tt (l₀ l : list bool) (n e : ℕ) := ⟦e⟧^((l₀ ++ l).nth) n = some tt

def extendable₀_le_0prime (l₀ : list bool) (n): 
  {e | ∃ l, extendable l₀ l n e} ≤ₜ ∅′ :=
by sorry

@[simp] theorem ε_operator_chr_Prop {β} [primcodable β] [inhabited β]
  (p : β → Prop) (h : (ε_operator (chr p)).dom) :
  p ((ε_operator (chr p)).get h) :=
by { have := roption.get_mem h, have := ε_witness this, simp at this, exact this }


theorem ε_operator_chr_Prop_iff {β} [primcodable β] [inhabited β]
  (p : β → Prop) :
  (∃ a, p a) ↔ (∃ a, a ∈ ε_operator (chr p)) :=
by simp[←roption.dom_iff_mem]

noncomputable def I : ℕ →. list bool × list bool
| 0 := some ([], [])
| (e+1) := do
    σ  ← I e,
    σ₁ ← cond (chr {e | ∃ l, extendable σ.2 l σ.1.length e} e)
          (do l ← ε_operator (chr $ λ l, extendable σ.2 l σ.1.length e),
              b ← (⟦e⟧^((σ.2 ++ l).nth) σ.1.length : roption bool),
              some (σ.1 ++ [!b], σ.2 ++ l))
          (some (σ.1 ++ [ff], σ.2)),
    σ₂ ← cond (chr {e | ∃ l, extendable σ₁.1 l σ₁.2.length e} e)
          (do l ← ε_operator (chr $ λ l, extendable σ₁.1 l σ₁.2.length e),
              b ← (⟦e⟧^((σ₁.1 ++ l).nth) σ₁.2.length : roption bool),
              some (σ₁.1 ++ l, σ₁.2 ++ [!b]))
          (some (σ₁.1, σ₁.2 ++ [ff])),
    some σ₂

theorem I_defined (s) : (I s).dom :=
begin
  induction s with s0 ih; simp [I, bind_dom],
  refine ⟨ih, _⟩,
  cases c₀ : chr {e | ∃ l, extendable ((I s0).get ih).snd l ((I s0).get ih).fst.length e} s0; simp [roption.some],
  { cases c₁ : chr {e | ∃ l, extendable (((I s0).get ih).fst ++ [ff]) l ((I s0).get ih).snd.length e} s0; simp [roption.some],
    simp[set.set_of_app_iff] at c₀ c₁,
    refine ⟨c₁, _⟩, simp[extendable] at c₁ ⊢, 
    let p := λ l, (⟦s0⟧^((((I s0).get ih).fst ++ ff :: l).nth) ((I s0).get ih).snd.length : roption bool).dom,
    have := ε_operator_chr_Prop p, exact this _ },
  { simp[set.set_of_app_iff] at c₀,
    let p := λ l, extendable ((I s0).get ih).snd l ((I s0).get ih).fst.length s0,
    refine ⟨⟨c₀,_⟩, _⟩, 
    { have := ε_operator_chr_Prop p, exact this _ },
    { have : ∃ l, l ∈ ε_operator (chr p) := (ε_operator_chr_Prop_iff p).mp c₀,
      rcases this with ⟨lb, hlb⟩, simp[p] at hlb, 
      have hb := ε_witness hlb, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
      rcases hb with ⟨b, hb⟩,
      simp[roption.eq_some_iff.mpr hlb, roption.eq_some_iff.mpr hb],
      cases c₁ : chr {e | ∃ l, extendable (((I s0).get ih).fst ++ [!b]) l (((I s0).get ih).snd.length + lb.length) e} s0; simp[roption.some],
      simp[set.set_of_app_iff] at c₁,
      refine ⟨c₁, _⟩, simp[extendable] at c₁ ⊢, 
      let p := λ (l : list bool), (⟦s0⟧^((((I s0).get ih).fst ++ !b :: l).nth) (((I s0).get ih).snd.length + lb.length)).dom,
      have := ε_operator_chr_Prop p, simp[p] at this, exact this c₁ } }
end

def I₀ : set ℕ := {n | ∃ s, ((I s).get (I_defined s)).1.nth n = tt}  
def I₁ : set ℕ := {n | ∃ s, ((I s).get (I_defined s)).2.nth n = tt}

lemma inconparable01 : I₀ ≰ₜ I₁ :=
begin
  assume h : I₀ ≤ₜ I₁,
  have l0 : ↑(chr I₀) partrec_in ↑(chr I₁) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧^(chr* I₁) = ↑(chr I₀) := rpartrec.rpartrec_univ_iff_total.mp l0,
  rcases this with ⟨e, he⟩,
  sorry

end

theorem Kleene_Post : ∃ (A B : set ℕ), (A ≤ₜ ∅′) ∧ (B ≤ₜ ∅′) ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end Kleene_Post

theorem Friedberg_Muchnik : ∃ (A B : set ℕ), re_pred A ∧ re_pred B ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end t_reducible