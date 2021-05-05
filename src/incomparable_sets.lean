import reducibility computable_function

open encodable denumerable roption

lemma list.append_nth_some {α} {l₀ : list α} {n a} (h : l₀.nth n = some a) (l₁) :
  (l₀ ++ l₁).nth n = some a :=
by { have := list.nth_eq_some.mp h, rcases this with ⟨en, _⟩,
     exact eq.trans (list.nth_append en) h, }


namespace t_reducible

--inductive list.initial {α} : list α → list α → Prop
--| refl {l}   : list.initial l l
--| cons {l a} : list.initial l (a :: l)
--| trans {l₀ l₁ l₂} : list.initial l₀ l₁ → list.initial l₁ l₂ → list.initial l₀ l₂

def list.initial {α} (l₀ l₁ : list α) := ∀ n a, l₀.rnth n = some a → l₁.rnth n = some a
infix ` ≺ `:50 := list.initial

theorem initial_append {α} (l l₀ : list α) : l ≺ l₀ ++ l := λ n b h,
by { simp[list.initial, list.rnth] at h ⊢, simp only [list.append_nth_some h] } 

@[simp] theorem initial_cons {α} (a) (l : list α) : l ≺ a :: l := λ n b h,
by { simp[list.initial, list.rnth] at h ⊢, simp only [list.append_nth_some h] } 

def limit (l : ℕ → list bool) := {n | ∃ s, (l s).rnth n = tt}

theorem initial_trans {α} {l₀ l₁ l₂ : list α} : l₀ ≺ l₁ → l₁ ≺ l₂ → l₀ ≺ l₂ :=
 λ h01 h12 _ _ e, h12 _ _ (h01 _ _ e) 

theorem initial_le {l : ℕ → list bool} (h : ∀ s, l s ≺ l (s + 1)) :
  ∀ {s t}, s ≤ t → l s ≺ l t :=
begin
  have l0 : ∀ s t, l s ≺ l (s + t),
  { intros s t, induction t with s0 ih generalizing s, simp[list.initial],
    simp[show s + s0.succ = (s + s0) + 1, from nat.add_succ _ _],
    exact initial_trans (ih _) (h _) },
  intros s t e,
  have : t = s + (t - s), omega,
  rw this, exact l0 _ _,
end 

theorem initial_limit {l : ℕ → list bool} (h : ∀ s, l s ≺ l (s + 1))
  {s n b} : (l s).rnth n = some b → chr (limit l) n = b := λ eb,
begin
  simp[limit], unfold_coes, cases b; simp[set.set_of_app_iff],
    { intros u c, have : s ≤ u ∨ u ≤ s, from le_total s u, cases this,
    have := initial_le h this _ _ eb, simp[c] at this, exact this,
    have := initial_le h this _ _ c, simp[eb] at this, exact this },
  refine ⟨s, eb⟩
end

theorem oracle_initial_limit {l : ℕ → list bool} (h : ∀ s, l s ≺ l (s + 1))
  {e s} {n : ℕ} {b : bool} :
  b ∈ (⟦e⟧^(l s).rnth n : roption bool) → 
  b ∈ (⟦e⟧^(chr* (limit l)) n : roption bool) := λ hs,
by { have := rpartrec.eval_inclusion hs, rcases this with ⟨u, hu⟩,
     apply hu, simp, exact λ _ _ _ e, initial_limit h e }

namespace Kleene_Post

def extendable (l₀ l : list bool) (n e : ℕ) := (⟦e⟧^((l ++ l₀).rnth) n : roption bool).dom
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

noncomputable def L : ℕ →. list bool × list bool
| 0     := some ([], [])
| (e+1) := do
    σ₀ ← L e,
    σ₁ ← cond (chr {e | ∃ l, extendable σ₀.2 l σ₀.1.length e} e)
          (do l ← ε_operator (chr $ λ l, extendable σ₀.2 l σ₀.1.length e),
              b ← (⟦e⟧^((l ++ σ₀.2).rnth) σ₀.1.length : roption bool),
              some (!b :: σ₀.1, l ++ σ₀.2))
          (some (ff :: σ₀.1, σ₀.2)),
    σ₂ ← cond (chr {e | ∃ l, extendable σ₁.1 l σ₁.2.length e} e)
          (do l ← ε_operator (chr $ λ l, extendable σ₁.1 l σ₁.2.length e),
              b ← (⟦e⟧^((l ++ σ₁.1).rnth) σ₁.2.length : roption bool),
              some (l ++ σ₁.1, !b :: σ₁.2))
          (some (σ₁.1, ff :: σ₁.2)),
    some σ₂

theorem I_defined (s) : (L s).dom :=
begin
  induction s with s0 ih; simp [L, bind_dom],
  refine ⟨ih, _⟩,
  cases c₀ : chr {e | ∃ l, extendable ((L s0).get ih).2 l ((L s0).get ih).1.length e} s0;
  simp [roption.some],
  { cases c₁ : chr {e | ∃ l, extendable (ff :: ((L s0).get ih).1) l ((L s0).get ih).2.length e} s0;
    simp [roption.some],
    simp[set.set_of_app_iff] at c₀ c₁,
    refine ⟨c₁, _⟩, simp[extendable] at c₁ ⊢, 
    let p := λ l, (⟦s0⟧^((l ++ ff :: ((L s0).get ih).1).rnth) ((L s0).get ih).2.length).dom,
    have := ε_operator_chr_Prop p, exact this _ },
  simp[set.set_of_app_iff] at c₀,
  let p := λ l, extendable ((L s0).get ih).2 l ((L s0).get ih).1.length s0,
  refine ⟨⟨c₀,_⟩, _⟩, 
  { have := ε_operator_chr_Prop p, exact this _ },
  { have : ∃ l, l ∈ ε_operator (chr p), { simp[←roption.dom_iff_mem], exact c₀ },
    rcases this with ⟨lb, hlb⟩, simp[p] at hlb, 
    have hb := ε_witness hlb, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp[roption.eq_some_iff.mpr hlb, roption.eq_some_iff.mpr hb],
    cases c₁ :
      chr {e | ∃ l, extendable (!b :: ((L s0).get _).1) l (lb.length + ((L s0).get _).2.length) e} s0;
    simp[roption.some],
    simp[set.set_of_app_iff] at c₁,
    refine ⟨c₁, _⟩, simp[extendable] at c₁ ⊢, 
    let p := λ l, (⟦s0⟧^((l ++ !b :: ((L s0).get ih).1).rnth) (lb.length + ((L s0).get ih).2.length)).dom,
    have := ε_operator_chr_Prop p, simp[p] at this, exact this c₁ }
end

noncomputable def L' (s) := (L s).get (I_defined s)

def I₀ : set ℕ := {n | ∃ s, (L' (s+1)).1.rnth n = tt}  
def I₁ : set ℕ := {n | ∃ s, (L' (s+1)).2.rnth n = tt}

theorem L'₀_include (s) :
  (L' s).1 ≺ (L' (s + 1)).1 :=
begin
  simp[L', L], simp[show L s = some (L' s), by simp[L']],
  cases C₀ : chr {e | ∃ l, extendable (L' s).2 l (L' s).1.length e} s; simp[C₀];
  simp [set.set_of_app_iff] at C₀,
  { cases C₁ : chr {e | ∃ l, extendable (ff :: (L' s).1) l (L' s).2.length e} s; simp[C₁],
    simp [set.set_of_app_iff] at C₁,
    let p := λ l, extendable (ff :: (L' s).1) l (L' s).2.length s,
    have : ∃ l, l ∈ ε_operator (chr p), { simp[←roption.dom_iff_mem], exact C₁ },
    rcases this with ⟨l₁, hl₁⟩, simp[p] at hl₁, 
    have := ε_witness hl₁, simp only [chr_iff, extendable, roption.dom_iff_mem] at this,
    rcases this with ⟨b₁, hb₁⟩,
    simp[roption.eq_some_iff.mpr hl₁, roption.eq_some_iff.mpr hb₁],
    rw (show l₁ ++ ff :: (L' s).1 = (l₁ ++ [ff]) ++ (L' s).1, by simp), exact initial_append _ _ },
  { let p := λ l, extendable (L' s).2 l (L' s).1.length s,
    have : ∃ l, l ∈ ε_operator (chr p), { simp[←roption.dom_iff_mem], exact C₀ },
    rcases this with ⟨l₀, hl₀⟩, simp[p] at hl₀, 
    have := ε_witness hl₀, simp only [chr_iff, extendable, roption.dom_iff_mem] at this,
    rcases this with ⟨b₀, hb₀⟩,
    simp[roption.eq_some_iff.mpr hl₀, roption.eq_some_iff.mpr hb₀],
    cases C₁ : chr {e | ∃ l, extendable (!b₀ :: (L' s).1) l (l₀.length + (L' s).2.length) e} s; simp[C₁],
    simp [set.set_of_app_iff] at C₁,
    let q := λ l, extendable (!b₀ :: (L' s).1) l (l₀.length + (L' s).2.length) s,
    have : ∃ l, l ∈ ε_operator (chr q), { simp[←roption.dom_iff_mem], exact C₁ },
    rcases this with ⟨l₁, hl₁⟩, simp[q] at hl₁, 
    have := ε_witness hl₁, simp only [chr_iff, extendable, roption.dom_iff_mem] at this,
    rcases this with ⟨b₁, hb₁⟩,
    simp[roption.eq_some_iff.mpr hl₁, roption.eq_some_iff.mpr hb₁],
    show (L' s).1 ≺ l₁ ++ !b₀ :: (L' s).1,
    rw (show l₁ ++ !b₀ :: (L' s).1 = l₁ ++ [!b₀] ++ (L' s).1, by simp),
    exact initial_append _ _ }
end

theorem L'₁_include (s) :
  (L' s).2 ≺ (L' (s + 1)).2 :=
begin
  simp[L', L], simp[show L s = some (L' s), by simp[L']],
  cases C₀ : chr {e | ∃ l, extendable (L' s).2 l (L' s).1.length e} s; simp[C₀];
  simp [set.set_of_app_iff] at C₀,
  { cases C₁ : chr {e | ∃ l, extendable (ff :: (L' s).1) l (L' s).2.length e} s; simp[C₁],
    simp [set.set_of_app_iff] at C₁,
    let p := λ l, extendable (ff :: (L' s).1) l (L' s).2.length s,
    have : ∃ l, l ∈ ε_operator (chr p), { simp[←roption.dom_iff_mem], exact C₁ },
    rcases this with ⟨l₁, hl₁⟩, simp[p] at hl₁, 
    have := ε_witness hl₁, simp only [chr_iff, extendable, roption.dom_iff_mem] at this,
    rcases this with ⟨b₁, hb₁⟩,
    simp[roption.eq_some_iff.mpr hl₁, roption.eq_some_iff.mpr hb₁] },
  { let p := λ l, extendable (L' s).2 l (L' s).1.length s,
    have : ∃ l, l ∈ ε_operator (chr p), { simp[←roption.dom_iff_mem], exact C₀ },
    rcases this with ⟨l₀, hl₀⟩, simp[p] at hl₀, 
    have := ε_witness hl₀, simp only [chr_iff, extendable, roption.dom_iff_mem] at this,
    rcases this with ⟨b₀, hb₀⟩,
    simp[roption.eq_some_iff.mpr hl₀, roption.eq_some_iff.mpr hb₀],
    cases C₁ : chr {e | ∃ l, extendable (!b₀ :: (L' s).1) l (l₀.length + (L' s).2.length) e} s; simp[C₁],
    { rw (show ff :: (l₀ ++ (L' s).2) = ([ff] ++ l₀) ++ (L' s).2, by simp), exact initial_append _ _ },
    simp [set.set_of_app_iff] at C₁,
    let q := λ l, extendable (!b₀ :: (L' s).1) l (l₀.length + (L' s).2.length) s,
    have : ∃ l, l ∈ ε_operator (chr q), { simp[←roption.dom_iff_mem], exact C₁ },
    rcases this with ⟨l₁, hl₁⟩, simp[q] at hl₁, 
    have := ε_witness hl₁, simp only [chr_iff, extendable, roption.dom_iff_mem] at this,
    rcases this with ⟨b₁, hb₁⟩,
    simp[roption.eq_some_iff.mpr hl₁, roption.eq_some_iff.mpr hb₁],
    rw (show !b₁ :: (l₀ ++ (L' s).2) = ([!b₁] ++ l₀) ++ (L' s).2, by simp),
    exact initial_append _ _ }
end



theorem gsgsg {e l} (hl : l ∈ ε_operator (chr $ λ l, extendable (L' e).2 l (L' e).1.length e)) :
  l ++ (L' e).2 ≺ (L' (e + 1)).2 :=
begin
  have := ε_witness hl, 
  simp only [chr_iff, set.set_of_app_iff, extendable, roption.dom_iff_mem] at  this,
  rcases this with ⟨b, hb⟩,
  have : chr {i : ℕ | ∃ (l : list bool), extendable (L' e).2 l (L' e).1.length i} e = tt,
  { simp[set.set_of_app_iff], exact C },
  simp[L', L], simp[this, show L e = some (L' e), by simp[L'],
  roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb],
  cases chr {e_1 : ℕ | ∃ (l : list bool), extendable (!b :: (L' e).1) l (l_1.length + (L' e).2.length) e_1} e,

end

theorem TT {e l₀ b₀ l₁ b₁}
  (hl₀ : l₀ ∈ ε_operator (chr $ λ l, extendable (L' e).2 l (L' e).1.length e))
  (hb₀ : b₀ ∈ (⟦e⟧^((l₀ ++ (L' e).2).rnth) (L' e).1.length : roption bool))
  (hl₁ : l₁ ∈ ε_operator (chr $ λ l, extendable (!b₀ :: (L' e).1) l (l₀.length + (L' e).2.length) e))
  (hb₁ : b₁ ∈ (⟦e⟧^((l₁ ++ (!b₀ :: (L' e).1)).rnth) (l₀.length + (L' e).2.length) : roption bool)) :
L' (e + 1) = ((l₁ ++ !b₀ :: (L' e).1, !b₁ :: (l₀ ++ (L' e).2))) :=
begin
  have hl₀' := ε_witness hl₀, simp at hl₀',
  have hl₁' := ε_witness hl₁, simp at hl₁',
  simp[L', L],
  simp[show L e = some (L' e), by simp[L']],
  have : chr {i | ∃ l, extendable (L' e).2 l (L' e).1.length i} e = tt,
  { simp[set.set_of_app_iff], exact ⟨l₀, hl₀'⟩ },
  simp[roption.eq_some_iff.mpr hl₀, roption.eq_some_iff.mpr hb₀, this],
  have : chr {i | ∃ l, extendable (!b₀ :: (L' e).1) l (l₀.length + (L' e).2.length) i} e = tt,
  { simp[set.set_of_app_iff], exact ⟨l₁, hl₁'⟩ },
  simp[roption.eq_some_iff.mpr hl₁, roption.eq_some_iff.mpr hb₁, this]
end



theorem preservationd₀ {e b} {n : ℕ}
  (hb : b ∈ (⟦e⟧^(L' (e + 1)).2.rnth n : roption bool) ) :
  b ∈ (⟦e⟧^(chr* I₁) n : roption bool) :=
begin
  simp[I₁],
  have := rpartrec.eval_inclusion hb, rcases this with ⟨s, hs⟩,
  apply hs, simp, intros x c ex ec,
  cases c; simp [set.set_of_app_iff],
end


theorem preservation₀ {e l₀ b₀}
  (hl : l₀ ∈ ε_operator (chr (λ l, extendable (L' e).2 l (L' e).1.length e))) 
  (hb : b₀ ∈ (⟦e⟧^((l₀ ++ (L' e).2).rnth) (L' e).1.length : roption bool)) :
  b₀ ∈ (⟦e⟧^(L' (e + 1)).2.rnth (L' e).1.length : roption bool) :=
begin
  have hl' := ε_witness hl, simp at hl',
  have := rpartrec.eval_inclusion hb, rcases this with ⟨s, hs⟩,
  apply hs, intros x c ex ec,
  simp[L', L], simp[show L e = some (L' e), by simp[L']],
  have : chr {i | ∃ l, extendable (L' e).2 l (L' e).1.length i} e = tt,
  { simp [set.set_of_app_iff], exact ⟨l₀, hl'⟩ },
  simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb, this],
  cases C : chr {i : ℕ | ∃ l, extendable (!b₀ :: (L' e).1) l (l₀.length + (L' e).2.length) i} e; simp[C],
  { simp [list.rnth, -list.append_assoc] at ec ⊢, 
    simp only [list.append_nth_some ec] },
  { let p := λ l, extendable (!b₀ :: (L' e).1) l (l₀.length + (L' e).2.length) e,
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr p), { simp[←roption.dom_iff_mem], exact C }, 
    rcases this with ⟨l₁, hl₁⟩, simp[p] at hl₁, 
    have := ε_witness hl₁, simp only [chr_iff, extendable, roption.dom_iff_mem] at this,
    rcases this with ⟨b₁, hb₁⟩,
    simp[roption.eq_some_iff.mpr hl₁, roption.eq_some_iff.mpr hb₁],
    show (!b₁ :: (l₀ ++ (L' e).2)).rnth x = some c,
    { simp[list.rnth, -list.append_assoc] at ec ⊢,
      simp only [list.append_nth_some ec] } }
end
  

theorem L'_prop (e) (h : ∃ l, extendable (L' e).2 l (L' e).1.length e) :
  ((L' (e + 1)).1.rnth ((L' e).1.length) : roption bool) = (⟦e⟧^(chr* I₁) ((L' e).1.length)).map bnot :=
begin
  simp[L', L], simp[show L e = some (L' e), by simp[L']],

end

lemma incomparable₀ : I₀ ≰ₜ I₁ :=
begin
  assume h : I₀ ≤ₜ I₁,
  have l0 : ↑(chr I₀) partrec_in ↑(chr I₁) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧^(chr* I₁) = ↑(chr I₀) := rpartrec.rpartrec_univ_iff_total.mp l0,
  rcases this with ⟨e, he⟩,
  let n := (L' e).1.length,
  have E : (chr I₀ n) ∈ (⟦e⟧^(chr* I₁ ) n : roption bool), simp[he],
  let p := λ l, extendable (L' e).2 l (L' e).1.length e,
  cases C₀ : chr {e | ∃ l, extendable (L' e).2 l (L' e).1.length e} e,
  { have div : ¬∃ l b, b ∈ (⟦e⟧^((l ++ (L' e).2).rnth) (L' e).1.length : roption bool),
    { simp only [chr_ff_iff, set.set_of_app_iff, extendable, 
      roption.dom_iff_mem] at C₀, exact C₀ },
    have := rpartrec.eval_inclusion E, rcases this with ⟨s, hs⟩, simp at hs,
    rcases L'_extend s e with ⟨l, hl⟩, 
    have : chr I₀ n ∈ (⟦e⟧^((l ++ (L' e).2).rnth) n : roption bool), 
    { have : ∀ x y, x < s → chr I₁ x = y → (l ++ (L' e).2).rnth x = some y,
      { intros x y e h, apply hl, simp[e, h], refl },
      from hs this },
    show false, from div ⟨l, chr I₀ n, this⟩ },
  have : ∃ (l : list bool), extendable (L' e).2 l (L' e).1.length e,
  { simp only [chr_iff, set.set_of_app_iff, roption.dom_iff_mem] at C₀, exact C₀ },
  have : ∃ l, l ∈ ε_operator (chr p), { simp[←roption.dom_iff_mem], exact this },
  rcases this with ⟨l₀, hl₀⟩, simp[p] at hl₀, 
  have hb := ε_witness hl₀, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
  rcases hb with ⟨b₀, hb₀⟩,


  have l0 : chr I₀ n = !b₀,
  { simp[I₀, L', L], 
    have : chr {i : ℕ | ∃ (l : list bool), extendable (L' e).2 l (L' e).1.length i} e = tt,
    { simp[set.set_of_app_iff], exact this },
    simp[this, show L e = some (L' e), by simp[L'],
    roption.eq_some_iff.mpr hl₀,roption.eq_some_iff.mpr hb₀],
      }

end

theorem Kleene_Post : ∃ (A B : set ℕ), (A ≤ₜ ∅′) ∧ (B ≤ₜ ∅′) ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end Kleene_Post

theorem Friedberg_Muchnik : ∃ (A B : set ℕ), re_pred A ∧ re_pred B ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end t_reducible