import reducibility computable_function

open encodable denumerable roption

local attribute [simp] set.set_of_app_iff

lemma bnot_ne (b) : b ≠ !b := by cases b; simp

lemma list.append_nth_some {α} {l₀ : list α} {n a} (h : l₀.nth n = some a) (l₁) :
  (l₀ ++ l₁).nth n = some a :=
by { have := list.nth_eq_some.mp h, rcases this with ⟨en, _⟩,
     exact eq.trans (list.nth_append en) h, }

lemma list.drop_nth {α} : ∀ (l : list α) (k n), (l.drop k).nth n = l.nth (n + k)
| []        _       _ := by simp [list.drop]
| (l :: ls) 0       _ := by simp [list.drop]
| (l :: ls) (k + 1) n := 
    by { simp [list.drop], have := list.drop_nth ls k n, simp [this], exact rfl }

namespace t_reducible

def list.initial (l₀ l₁ : list bool) := ∀ n, l₀.rnth n = some tt → l₁.rnth n = some tt
infix ` ≼ `:50 := list.initial

@[simp] theorem initial_refl (l : list bool) : l ≼ l :=
by simp[list.initial]

@[simp] theorem initial_append (l l₀ : list bool) : l ≼ l₀ ++ l := λ n h,
by { simp[list.initial, list.rnth] at h ⊢, simp only [list.append_nth_some h] } 

@[simp] theorem initial_cons (a) (l : list bool) : l ≼ a :: l := λ n h,
by { simp[list.initial, list.rnth] at h ⊢, simp only [list.append_nth_some h] } 

theorem suffix_initial {l₀ l₁ : list bool} : l₀ <:+ l₁ → l₀ ≼ l₁ :=
by { simp[list.is_suffix], intros l hl s h₀,
     simp[←hl, list.rnth] at h₀ ⊢, rcases list.nth_eq_some.mp h₀ with ⟨e, _⟩,
     simp [list.nth_append e, h₀] }

def limit (L : ℕ → list bool) := {n | ∃ s, (L s).rnth n = tt}

-- finite initial segments
def fis (L : ℕ → list bool) := ∀ s, L s ≼ L (s + 1)

def total {α} (L : ℕ → list α) := ∀ n, ∃ s, ∀ u, s < u → n < (L u).length

theorem initial_trans {l₀ l₁ l₂ : list bool} : l₀ ≼ l₁ → l₁ ≼ l₂ → l₀ ≼ l₂ :=
 λ h01 h12 _ e, h12 _ (h01 _ e)

lemma relation_path_le {α} {p : ℕ → α} (R : α → α → Prop)
  (r : ∀ a, R a a) (t : ∀ a b c, R a b → R b c → R a c)
  (i : ∀ n, R (p n) (p (n+1))) : 
  ∀ s t, s ≤ t → R (p s) (p t) :=
begin
  have l0 : ∀ s t, R (p s) (p (s + t)),
  { intros s t, induction t with s0 ih generalizing s, simp[list.initial, r],
    simp[show s + s0.succ = (s + s0) + 1, from nat.add_succ _ _],
    exact t _ _ _ (ih _) (i _) },
  intros s t e,
  have : t = s + (t - s), omega,
  rw this, exact l0 _ _,
end

theorem initial_le {L : ℕ → list bool} (h : fis L) :
  ∀ {s t}, s ≤ t → L s ≼ L t := 
relation_path_le (≼) (by simp) (λ a b c, initial_trans) h

theorem fis_limit_eq {L : ℕ → list bool} (F : fis L) (m) :
  limit L = limit (λ x, L (x + m)) := funext $ λ n,
begin
  simp[limit, set.set_of_app_iff], split,
  { rintros ⟨s, hs⟩, have : s ≤ m ∨ m < s, from le_or_lt s m,
    cases this,
    refine ⟨0, _⟩, simp,
    exact initial_le F this _ hs,
    refine ⟨s-m, _⟩,  have : s - m + m = s, omega, simp[this],
    exact hs },
  { rintros ⟨s, hs⟩, refine ⟨s+m, hs⟩ }
end

def subseq (A B : ℕ → option bool) := ∀ n b, A n = some b → B n = some b

infix ` ⊆. `:50 := subseq

lemma suffix_subseq {l₀ l₁ : list bool} (h : l₀ <:+ l₁) :
  l₀.rnth ⊆. l₁.rnth := λ n b eb,
by { rcases h with ⟨l, hl⟩,
     simp [←hl, list.rnth], exact list.append_nth_some eb _ }

theorem subseq_limit (C : ℕ → option bool) :
  ∀ {L : ℕ → list bool}, fis L → (∃ s, ∀ u, s ≤ u → C ⊆. (L u).rnth) → C ⊆. chr* limit L := 
begin
  suffices : 
    ∀ {L : ℕ → list bool}, (∀ u, C ⊆. (L u).rnth) → C ⊆. chr* limit L,
  { rintros L F ⟨s, hs⟩, 
     rw fis_limit_eq F s,
     apply this, intros u,
     apply hs, omega },
  intros L h n b, 
  cases b; simp [limit]; unfold_coes,
  { intros hn s hs, have := h s _ _ hn, simp [hs] at this,  exact this },
  { intros hn, refine ⟨0, h 0 _ _ hn⟩ }
end

lemma initial_subseq {l : list bool} {A : ℕ → bool} (hl : l.rnth ⊆. (λ x, A x)) (s) :
  ∃ l₀, (initial_code A s).rnth ⊆. (l₀ ++ l).rnth :=
begin
  refine ⟨((initial_code A s).reverse.drop l.length).reverse, _⟩,
  simp[list.rnth], intros m c ec,
  have hA := initial_code_some ec, 
  have em : m < l.reverse.length ∨ l.reverse.length ≤ m, exact lt_or_ge _ _, 
  cases em,
  { simp[list.nth_append em], 
    have ll := list.nth_le_nth em, 
    have := hl _ _ ll, unfold_coes at this, simp at this,
    simp [←this] at ll, simp [ll, hA] },
  { simp [list.nth_append_right em], 
    have : m - l.length + l.length = m, { simp at em, omega },
    simp [list.drop_nth, this], exact ec }
end

namespace Kleene_Post

def extendable (l₀ l : list bool) (n e : ℕ) := (⟦e⟧^((l ++ l₀).rnth) n : roption bool).dom

theorem extendable_suffix {l₀ n e} {A : ℕ → bool}
  (h : ∀ l, ¬extendable l₀ l n e) (hl₀ : l₀.rnth ⊆. (λ x, A x)) :
  ¬(⟦e⟧^(λ x, some (A x)) n : roption bool).dom :=
begin
  intros C,
  simp [extendable] at h,
  rcases roption.dom_iff_mem.mp C with ⟨b, hb⟩,
  rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩,
  have := initial_subseq hl₀ s, rcases this with ⟨l, hl⟩,
  suffices : b ∈ (⟦e⟧^((l ++ l₀).rnth) n : roption bool),
  { rcases this with ⟨lmm, _⟩, exact h _ lmm },
  apply hs, simp, intros m c em hc,
  have : (initial_code (λ (x : ℕ), A x) s).rnth m = c, simp[em, hc],
  exact hl _ _ this
end

def extendable₀_le_0prime (l₀ : list bool) (n): 
  {e | ∃ l, extendable l₀ l n e} ≤ₜ ∅′ :=
by sorry

noncomputable def L : ℕ →. list bool × list bool
| 0     := some ([], [])
| (s+1) :=
  let e := s.div2 in
  match s.bodd with
  | ff := do
    σ ← L s,
    cond (chr {e | ∃ l, extendable σ.2 l σ.1.length e} e)
      (do l ← ε_operator (chr $ λ l, extendable σ.2 l σ.1.length e),
          b ← (⟦e⟧^((l ++ σ.2).rnth) σ.1.length : roption bool),
          some (!b :: σ.1, l ++ σ.2))
      (some (ff :: σ.1, σ.2))
  | tt := do
    σ ← L s,
    cond (chr {e | ∃ l, extendable σ.1 l σ.2.length e} e)
      (do l ← ε_operator (chr $ λ l, extendable σ.1 l σ.2.length e),
          b ← (⟦e⟧^((l ++ σ.1).rnth) σ.2.length : roption bool),
          some (l ++ σ.1, !b :: σ.2))
      (some (σ.1, ff :: σ.2))
  end

theorem I_defined : ∀ s, (L s).dom 
| 0     := by simp[L]
| (s+1) :=
  let e := s.div2 in
  have IH : _ := I_defined s,
  begin
    simp[L], cases M : s.bodd; simp[M, L],
    { refine ⟨IH, _⟩,
      cases C : chr {i | ∃ l, extendable ((L s).get IH).snd l ((L s).get IH).fst.length i} e;
      simp [C], simp [set.set_of_app_iff] at C, refine ⟨C, _⟩,
      have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable ((L s).get IH).2 l ((L s).get IH).1.length e),
      { simp[←roption.dom_iff_mem], exact C },
      rcases this with ⟨l, hl⟩,
      have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
      rcases hb with ⟨b, hb⟩,
      simp[roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb, roption.some] },    
    { refine ⟨IH, _⟩,
      cases C : chr {i | ∃ l, extendable ((L s).get IH).fst l ((L s).get IH).snd.length i} e;
      simp [C], simp [set.set_of_app_iff] at C, refine ⟨C, _⟩,
      have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable ((L s).get IH).fst l ((L s).get IH).snd.length e),
      { simp[←roption.dom_iff_mem], exact C },
      rcases this with ⟨l, hl⟩,
      have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
      rcases hb with ⟨b, hb⟩,
      simp[roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb, roption.some] }
  end

noncomputable def L₀ (s) := ((L s).get (I_defined s)).1
noncomputable def L₁ (s) := ((L s).get (I_defined s)).2

def I₀ : set ℕ := limit L₀
def I₁ : set ℕ := limit L₁

theorem L₀_suffix (s) :
  (L₀ s) <:+ (L₀ (s+1)) :=
begin
  let e := s.div2,
  simp[fis, L₀, L], cases M : s.bodd; simp [M, L, show L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { cases C : chr {e | ∃ l, extendable (L₁ s) l (L₀ s).length e} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₁ s) l (L₀ s).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },  
  { cases C : chr {i | ∃ l, extendable (L₀ s) l (L₁ s).length i} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₀ s) l (L₁ s).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] }
end

theorem L₀_fis : fis L₀ := λ s, suffix_initial (L₀_suffix s)

theorem L₁_suffix (s) :
  (L₁ s) <:+ (L₁ (s+1)) :=
begin
  let e := s.div2,
  simp[fis, L₁, L], cases M : s.bodd; simp [M, L, show L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { cases C : chr {i | ∃ l, extendable (L₁ s) l (L₀ s).length i} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₁ s) l (L₀ s).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },  
  { cases C : chr {i | ∃ l, extendable (L₀ s) l (L₁ s).length i} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₀ s) l (L₁ s).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] }
end

theorem L₁_fis : fis L₁ := λ s, suffix_initial (L₁_suffix s)

theorem initial_suffix₀ : ∀ {s t}, s ≤ t → L₀ s <:+ L₀ t := 
relation_path_le (<:+) list.suffix_refl (λ a b c, list.is_suffix.trans) L₀_suffix

theorem initial_suffix₁ : ∀ {s t}, s ≤ t → L₁ s <:+ L₁ t := 
relation_path_le (<:+) list.suffix_refl (λ a b c, list.is_suffix.trans) L₁_suffix

lemma L₀_subseq (s) : (L₀ s).rnth ⊆. chr* I₀ :=
begin
  have := subseq_limit (L₀ s).rnth L₀_fis,
  apply this,
  refine ⟨s, λ u eu, _⟩,
  exact suffix_subseq (initial_suffix₀ eu)
end

lemma L₁_subseq (s) : (L₁ s).rnth ⊆. chr* I₁ :=
begin
  have := subseq_limit (L₁ s).rnth L₁_fis,
  apply this,
  refine ⟨s, λ u eu, _⟩,
  exact suffix_subseq (initial_suffix₁ eu)
end

lemma requirement₀ (e) : ∃ w : ℕ,
  ¬(⟦e⟧^(chr* I₁) w : roption bool).dom ∨ !chr I₀ w ∈ (⟦e⟧^(chr* I₁) w : roption bool) :=
begin
  use (L₀ (2*e)).length,
  cases C : (chr {i | ∃ l, extendable (L₁ (2*e)) l (L₀ (2*e)).length i} e),
  { left, simp at C,
    have : (L₁ (2*e)).rnth ⊆. chr* I₁, from L₁_subseq _,
    exact extendable_suffix C this },
  { right,
    show !chr I₀ (L₀ (2*e)).length ∈ ⟦e⟧^(chr* I₁) (L₀ (2 * e)).length,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₁ (2*e)) l (L₀ (2*e)).length e),
    { simp[←roption.dom_iff_mem] at C ⊢, exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    have : L₀ (2*e + 1) = !b :: L₀ (2*e) ∧ L₁ (2*e + 1) = l ++ L₁ (2*e),
    { simp [L₀, L₁, L, show (2 * e).div2 = e, by simp[nat.div2_val]], 
      simp [L, show L (2*e) = some (L₀ (2*e), L₁ (2*e)), by simp[L₀, L₁], C,
        roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },
    rcases this with ⟨nL₀, nL₁⟩,
    have lmm0 : chr I₀ (L₀ (2 * e)).length = !b,
    { have := L₀_subseq (2*e + 1) ((L₀ (2*e)).length) (!b),
      simp [nL₀, list.rnth] at this, apply this,
      rw (show (L₀ (2*e)).length = (L₀ (2*e)).reverse.length, by simp),
      simp only [list.nth_concat_length] },
    have lmm1 : b ∈ (⟦e⟧^(chr* I₁) (L₀ (2*e)).length : roption bool),
    { rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩, apply hs, simp,
      have := L₁_subseq (2*e + 1), simp[nL₁, subseq] at this,
      exact (λ n c _, this n c) },
    simp[lmm0, lmm1] }
end

lemma requirement₁ (e) : ∃ w : ℕ,
  ¬(⟦e⟧^(chr* I₀) w : roption bool).dom ∨ !chr I₁ w ∈ (⟦e⟧^(chr* I₀) w : roption bool) :=
begin
  let i := bit1 e,  
  use (L₁ i).length,
  cases C : (chr {j | ∃ l, extendable (L₀ i) l (L₁ i).length j} e),
  { left, simp at C,
    have : (L₀ i).rnth ⊆. chr* I₀, from L₀_subseq _,
    exact extendable_suffix C this },
  { right,
    show !chr I₁ (L₁ i).length ∈ ⟦e⟧^(chr* I₀) (L₁ i).length,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₀ i) l (L₁ i).length e),
    { simp[←roption.dom_iff_mem] at C ⊢, exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    have : L₀ (i + 1) = l ++ L₀ i ∧ L₁ (i + 1) = !b :: L₁ i,
    { simp [L₀, L₁, L, show i.div2 = e, by simp[i]], 
      simp [L, show L i = some (L₀ i, L₁ i), by simp[L₀, L₁], C,
        roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },
    rcases this with ⟨nL₀, nL₁⟩,
    have lmm0 : chr I₁ (L₁ i).length = !b,
    { have := L₁_subseq (i+ 1) ((L₁ i).length) (!b),
      simp [nL₁, list.rnth] at this, apply this,
      rw (show (L₁ i).length = (L₁ i).reverse.length, by simp),
      simp only [list.nth_concat_length] },
    have lmm1 : b ∈ (⟦e⟧^(chr* I₀) (L₁ i).length : roption bool),
    { rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩, apply hs, simp,
      have := L₀_subseq (i + 1), simp[nL₀, subseq] at this,
      exact (λ n c _, this n c) },
    simp[lmm0, lmm1] }
end

lemma incomparable₀ : I₀ ≰ₜ I₁ :=
begin
  assume h : I₀ ≤ₜ I₁,
  have l0 : ↑(chr I₀) partrec_in ↑(chr I₁) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧^(chr* I₁) = ↑(chr I₀) := rpartrec.rpartrec_univ_iff_total.mp l0,
  rcases this with ⟨e, he⟩,
  have E : ∀ n, (chr I₀ n) ∈ (⟦e⟧^(chr* I₁ ) n : roption bool), simp[he],
  rcases requirement₀ e with ⟨w, hw⟩, cases hw,
  { have : (⟦e⟧^(chr* I₁) w).dom, { rcases E w with ⟨h, _⟩, exact h },
    contradiction },
    have : chr I₀ w = !chr I₀ w := roption.mem_unique (E w) hw,
  show false, from bnot_ne _ this
end

lemma incomparable₁ : I₁ ≰ₜ I₀ :=
begin
  assume h : I₁ ≤ₜ I₀,
  have l0 : ↑(chr I₁) partrec_in ↑(chr I₀) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧^(chr* I₀) = ↑(chr I₁) := rpartrec.rpartrec_univ_iff_total.mp l0,
  rcases this with ⟨e, he⟩,
  have E : ∀ n, (chr I₁ n) ∈ (⟦e⟧^(chr* I₀ ) n : roption bool), simp[he],
 rcases requirement₁ e with ⟨w, hw⟩, cases hw,
  { have : (⟦e⟧^(chr* I₀) w).dom, { rcases E w with ⟨h, _⟩, exact h },
    contradiction },
    have : chr I₁ w = !chr I₁ w := roption.mem_unique (E w) hw,
  show false, from bnot_ne _ this
end

theorem Kleene_Post : ∃ (I₀ I₁ : set ℕ), (I₀ ≤ₜ ∅′) ∧ (I₁ ≤ₜ ∅′) ∧ (I₀ ≰ₜ I₁) ∧ (I₁ ≰ₜ I₀) :=
by sorry

end Kleene_Post

theorem Friedberg_Muchnik : ∃ (A B : set ℕ), re_pred A ∧ re_pred B ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end t_reducible