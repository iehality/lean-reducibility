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

lemma relation_path_le {α} {p : ℕ → α} (R : α → α → Prop)
  (r : ∀ a, R a a) (t : ∀ a b c, R a b → R b c → R a c)
  (i : ∀ n, R (p n) (p (n+1))) : 
  ∀ s t, s ≤ t → R (p s) (p t) :=
begin
  have l0 : ∀ s t, R (p s) (p (s + t)),
  { intros s t, induction t with s0 ih generalizing s, simp[r],
    simp[show s + s0.succ = (s + s0) + 1, from nat.add_succ _ _],
    exact t _ _ _ (ih _) (i _) },
  intros s t e,
  have : t = s + (t - s), omega,
  rw this, exact l0 _ _,
end

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

theorem limit_computabile_in_jump {L : ℕ → list bool} {A : set ℕ} (cL : L computable_in chr. A) :
  limit L ≤ₜ A′ :=
begin
  let f : ℕ × ℕ →. ℕ := (λ n, cond ((L n.2).rnth n.1 = tt) (some 0) none),
  have lmm0 : f partrec_in chr. A,
  { apply rpartrec.cond,
    { have := primrec.list_nth.to_comp.to_rcomp.comp 
        ((primrec.list_reverse.to_comp.to_rcomp.comp $
          cL.comp rcomputable.snd).pair rcomputable.fst),
      have := this.pair (rcomputable.const (some tt)),
      have := primrec.eq.to_comp.to_rcomp.comp this,
      exact this },
    exact rcomputable.const _,
    exact partrec.none.to_rpart },
  have eqn0 : limit L = {n | ∃ s, (f (n, s)).dom},
  { apply set.ext, intros n, simp [limit, f],
    split; rintros ⟨s, hs⟩; refine ⟨s, _⟩,
    { simp [hs] },
    { by_cases (L s).rnth n = ↑tt, exact h,
      exfalso, simp [h] at hs, exact eq_none_iff'.mp rfl hs } },
  have : {x | ∃ y, (f (x, y)).dom} ≤ₜ A′ := rpartrec_dom_exists_prime lmm0,
  rw eqn0, exact this
end

-- finite initial segments
def fis (L : ℕ → list bool) := ∀ s, L s ≼ L (s + 1)

def total {α} (L : ℕ → list α) := ∀ n, ∃ s, ∀ u, s < u → n < (L u).length

theorem initial_trans {l₀ l₁ l₂ : list bool} : l₀ ≼ l₁ → l₁ ≼ l₂ → l₀ ≼ l₂ :=
 λ h01 h12 _ e, h12 _ (h01 _ e)


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

def extendable (l₀ l : list bool) (n e : ℕ) := (⟦e⟧ᵪ^((l ++ l₀).rnth) n).dom

theorem extendable_suffix {l₀ n e} {A : ℕ → bool}
  (h : ∀ l, ¬extendable l₀ l n e) (hl₀ : l₀.rnth ⊆. (λ x, A x)) :
  ¬(⟦e⟧ᵪ^(λ x, some (A x)) n).dom :=
begin
  intros C,
  simp [extendable] at h,
  rcases roption.dom_iff_mem.mp C with ⟨b, hb⟩,
  rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩,
  have := initial_subseq hl₀ s, rcases this with ⟨l, hl⟩,
  suffices : b ∈ (⟦e⟧ᵪ^((l ++ l₀).rnth) n),
  { rcases this with ⟨lmm, _⟩, exact h _ lmm },
  apply hs, simp, intros m c em hc,
  have : (initial_code (λ (x : ℕ), A x) s).rnth m = c, simp[em, hc],
  exact hl _ _ this
end

noncomputable def L : ℕ →. list bool × list bool
| 0     := some ([], [])
| (s+1) :=
  let e := s.div2 in
  match s.bodd with
  | ff := do
    σ ← L s,
    cond (chr {e | ∃ l, extendable σ.2 l σ.1.length e} e)
      (do l ← ε_operator (chr $ λ l, extendable σ.2 l σ.1.length e),
          b ← (⟦e⟧ᵪ^((l ++ σ.2).rnth) σ.1.length),
          some (!b :: σ.1, l ++ σ.2))
      (some (ff :: σ.1, σ.2))
  | tt := do
    σ ← L s,
    cond (chr {e | ∃ l, extendable σ.1 l σ.2.length e} e)
      (do l ← ε_operator (chr $ λ l, extendable σ.1 l σ.2.length e),
          b ← (⟦e⟧ᵪ^((l ++ σ.1).rnth) σ.2.length),
          some (l ++ σ.1, !b :: σ.2))
      (some (σ.1, ff :: σ.2))
  end
#check rpartrec.cond
#check rpartrec.eval_list_partrec ℕ bool


section
open primrec

lemma extendable_exists_comp0 : 
  {x : ℕ × list bool × ℕ | ∃ l, (⟦x.1⟧ᵪ^(l ++ x.2.1).rnth x.2.2).dom} ≤ₜ ∅′ :=
begin
  let f := (λ (x : ℕ × list bool × ℕ) l, ⟦x.1⟧ᵪ^(l ++ x.2.1).rnth x.2.2),
  have := (fst.comp fst).pair ((list_append.comp snd (fst.comp $ snd.comp fst)).pair
    (snd.comp $ snd.comp fst)),
  have : partrec₂ f := (rpartrec.eval_list_partrec ℕ bool).comp this.to_comp,
  have := partrec_dom_exists_0prime this,
  exact this
end

def K_string := {x : ℕ × list bool × ℕ | (⟦x.1⟧ᵪ^x.2.1.rnth x.2.2).dom}

lemma K_str_0prime_comp :
  K_string ≤ₜ ∅′ :=
partrec_dom_0prime (rpartrec.eval_list_partrec ℕ bool)

lemma L_rcomp_0prime'₀ :
  (λ (a : ℕ × list bool × list bool),
    ε_operator (chr (λ l, extendable a.2.1 l a.2.2.length a.1.div2)) >>=
    λ l, (⟦a.1.div2⟧ᵪ^((l ++ a.2.1).rnth) a.2.2.length >>=
    λ b, some (l ++ a.2.1, !b :: a.2.2))) partrec_in chr. ∅′ :=
begin
  let p := (λ x : (ℕ × list bool × list bool) × list bool,
    chr K_string (x.1.1.div2, x.2 ++ x.1.2.1, x.1.2.2.length)),
  have : ∀ a : ℕ × list bool × list bool,
    chr (λ l, (⟦a.1.div2⟧ᵪ^((l ++ a.2.1).rnth) a.2.2.length).dom) =
    λ l, p (a, l),
  { intros a, funext x, apply chr_ext.mpr, simp [K_string] }, simp [this],
  have lmm0 : (λ a, ε_operator (λ x, p (a, x))) partrec_in chr. ∅′,
  { have := (nat_div2.comp $ fst.comp fst).pair 
      ((list_append.comp snd (fst.comp $ snd.comp fst)).pair 
      (list_length.comp $ snd.comp $ snd.comp fst)),
    have := (classical_iff.mp K_str_0prime_comp).comp this.to_comp.to_rcomp,
    have : p computable_in chr. ∅′ := this,
    exact (rpartrec.ε_operator_rpartrec p).trans this },
  let g := λ x : (ℕ × list bool × list bool) × list bool,
    (⟦x.1.1.div2⟧ᵪ^((x.2 ++ x.1.2.1).rnth) x.1.2.2.length).bind
    (λ b, some (x.2 ++ x.1.2.1, !b :: x.1.2.2)),
  have lmm1 : partrec g,
  { let m := (λ x : (ℕ × list bool × list bool) × list bool,
      (x.1.1.div2, x.2 ++ x.1.2.1, x.1.2.2.length)),
    have pm : primrec m := (nat_div2.comp $ fst.comp fst).pair
      ((list_append.comp snd (fst.comp $ snd.comp fst)).pair
      (list_length.comp $ snd.comp $ snd.comp fst)),
    have lmm1 := (rpartrec.eval_list_partrec ℕ bool).comp pm.to_comp, simp [m] at lmm1,
    let h := (λ (x : (ℕ × list bool × list bool) × list bool) (b : bool),
      (x.2 ++ x.1.2.1, !b :: x.1.2.2)),
    have ph : primrec₂ h := (list_append.comp (snd.comp fst) 
      (fst.comp $ snd.comp $ fst.comp fst)).pair 
      (list_cons.comp (primrec.bnot.comp snd) (snd.comp $ snd.comp $ fst.comp fst)),
    exact lmm1.bind ph.to_comp.part },
  have := lmm0.bind lmm1.to_rpart, simp [g] at this,
  exact this
end

lemma L_rcomp_0prime'₁ :
  (λ (a : ℕ × list bool × list bool),
    ε_operator (chr (λ l, extendable a.2.2 l a.2.1.length a.1.div2)) >>=
    λ l, ⟦a.1.div2⟧ᵪ^((l ++ a.2.2).rnth) a.2.1.length >>=
    λ b, some (!b :: a.2.1, l ++ a.2.2)) partrec_in chr. ∅′ :=
begin
  simp [extendable],
  let p := (λ x : (ℕ × list bool × list bool) × list bool,
    chr K_string (x.1.1.div2, x.2 ++ x.1.2.2, x.1.2.1.length)),
  have : ∀ a : ℕ × list bool × list bool,
    chr (λ l, (⟦a.1.div2⟧ᵪ^((l ++ a.2.2).rnth) a.2.1.length).dom) =
    λ l, p (a, l),
  { intros a, funext x, apply chr_ext.mpr, simp [K_string] },
  have lmm0 : (λ a, ε_operator (λ x, p (a, x))) partrec_in chr. ∅′,
  { have := (nat_div2.comp $ fst.comp fst).pair 
      ((list_append.comp snd (snd.comp $ snd.comp fst)).pair 
      (list_length.comp $ fst.comp $ snd.comp fst)),
    have := (classical_iff.mp K_str_0prime_comp).comp this.to_comp.to_rcomp,
    have : p computable_in chr. ∅′ := this,
    exact (rpartrec.ε_operator_rpartrec p).trans this },
  let g := λ x : (ℕ × list bool × list bool) × list bool,
    (⟦x.1.1.div2⟧ᵪ^((x.2 ++ x.1.2.2).rnth) x.1.2.1.length).bind
    (λ b, some (!b :: x.1.2.1, x.2 ++ x.1.2.2)),
  have lmm1 : partrec g,
  { let m := (λ x : (ℕ × list bool × list bool) × list bool,
      (x.1.1.div2, x.2 ++ x.1.2.2, x.1.2.1.length)),
    have pm : primrec m := (nat_div2.comp $ fst.comp fst).pair
      ((list_append.comp snd (snd.comp $ snd.comp fst)).pair
      (list_length.comp $ fst.comp $ snd.comp fst)),
    have lmm1 := (rpartrec.eval_list_partrec ℕ bool).comp pm.to_comp, simp [m] at lmm1,
    let h := (λ (x : (ℕ × list bool × list bool) × list bool) (b : bool),
      (!b :: x.1.2.1, x.2 ++ x.1.2.2)),
    have ph : primrec₂ h := 
      (list_cons.comp (primrec.bnot.comp snd) (fst.comp $ snd.comp $ fst.comp fst)).pair
      (list_append.comp (snd.comp fst) (snd.comp $ snd.comp $ fst.comp fst)),
    exact lmm1.bind ph.to_comp.part },
  have := lmm0.bind lmm1.to_rpart, simp [g] at this,
  exact this
end

theorem L_rcomp_0prime : L partrec_in (chr. ∅′) :=
begin
  let h : ℕ × ℕ × (list bool × list bool) →. list bool × list bool := λ x,
    let s := x.2.1,
        σ := x.2.2,
        e := s.div2 in
    cond s.bodd
      (cond (chr {e | ∃ l, extendable σ.1 l σ.2.length e} e)
        (do l ← ε_operator (chr $ λ l, extendable σ.1 l σ.2.length e),
            b ← (⟦e⟧ᵪ^((l ++ σ.1).rnth) σ.2.length),
            some (l ++ σ.1, !b :: σ.2))
        (some (σ.1, ff :: σ.2)))    
      (cond (chr {e | ∃ l, extendable σ.2 l σ.1.length e} e)
        (do l ← ε_operator (chr $ λ l, extendable σ.2 l σ.1.length e),
            b ← (⟦e⟧ᵪ^((l ++ σ.2).rnth) σ.1.length),
            some (!b :: σ.1, l ++ σ.2))
        (some (ff :: σ.1, σ.2))),
  have : h partrec_in (chr. ∅′),
  { apply rpartrec.cond,
    { exact (primrec.nat_bodd.comp $ primrec.fst.comp primrec.snd).to_comp.to_rcomp },
    { apply rpartrec.cond,
      { have := (primrec.nat_div2.comp primrec.fst).pair ((primrec.fst.comp primrec.snd).pair 
          (primrec.list_length.comp $ primrec.snd.comp primrec.snd)),
        have := (classical_iff.mp extendable_exists_comp0).comp
          (this.comp primrec.snd).to_comp.to_rcomp,
        exact this },
      { exact L_rcomp_0prime'₀.comp rcomputable.snd }, 
      { have := (fst.comp $ snd.comp snd).pair 
          (list_cons.comp (const ff) (snd.comp $ snd.comp snd)),
        exact this.to_comp.to_rcomp } },
    { apply rpartrec.cond,
      { have := (primrec.nat_div2.comp primrec.fst).pair ((primrec.snd.comp primrec.snd).pair 
          (primrec.list_length.comp $ primrec.fst.comp primrec.snd)),
        have := (classical_iff.mp extendable_exists_comp0).comp
          (this.comp primrec.snd).to_comp.to_rcomp,
        exact this },
      { exact L_rcomp_0prime'₁.comp rcomputable.snd },
      { have := (list_cons.comp (const ff) (fst.comp $ snd.comp snd)).pair
          (snd.comp $ snd.comp snd),
        exact this.to_comp.to_rcomp } } },
  have := rpartrec.nat_elim (rcomputable.id)
    (rcomputable.const (([], []) : list bool × list bool)) this,
  exact (this.of_eq $ λ s, by 
  { simp, induction s with s0 ih; simp [L],
    cases C : s0.bodd; simp [C, L, h] at ih ⊢; rw ih; congr; funext; simp [C] })
end

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

lemma L₀_0'computable : L₀ computable_in chr. ∅′ :=
begin
  have := (rcomputable.total_computable I_defined),
  have : (λ (a : ℕ), (L a).get _) computable_in chr. ∅′ := rpartrec.trans this L_rcomp_0prime,
  exact rcomputable.fst.comp this,
end

lemma L₁_0'computable : L₁ computable_in chr. ∅′ :=
begin
  have := (rcomputable.total_computable I_defined),
  have : (λ (a : ℕ), (L a).get _) computable_in chr. ∅′ := rpartrec.trans this L_rcomp_0prime,
  exact rcomputable.snd.comp this,
end

theorem L₀_length (e) :
  (L₀ (bit0 e)).length < (L₀ (bit0 e + 1)).length :=
begin
  simp[fis, L₀, L], simp [L, show ∀ s, L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { cases C : chr {i | ∃ l, extendable (L₁ (bit0 e)) l (L₀ (bit0 e)).length i} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₁ (bit0 e)) l (L₀ (bit0 e)).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb ] }
end

theorem L₁_length (e) :
  (L₁ (bit1 e)).length < (L₁ (bit1 e + 1)).length :=
begin
  simp[fis, L₁, L], simp [L, show ∀ s, L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { cases C : chr {i | ∃ l, extendable (L₀ (bit1 e)) l (L₁ (bit1 e)).length i} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₀ (bit1 e)) l (L₁ (bit1 e)).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb ] }
end

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

theorem initial_suffix₀ : ∀ {s t}, s ≤ t → L₀ s <:+ L₀ t := 
relation_path_le (<:+) list.suffix_refl (λ a b c, list.is_suffix.trans) L₀_suffix

theorem initial_suffix₁ : ∀ {s t}, s ≤ t → L₁ s <:+ L₁ t := 
relation_path_le (<:+) list.suffix_refl (λ a b c, list.is_suffix.trans) L₁_suffix

theorem L₀_length_lt (e) :
  e < (L₀ (bit0 e + 1)).length :=
begin
  induction e with e0 ih,
  exact L₀_length 0, 
  have eq0 : (L₀ (bit0 e0 + 1)).length ≤ (L₀ (bit0 e0 + 1 + 1)).length,
    from list.length_le_of_infix (list.infix_of_suffix $ L₀_suffix $ bit0 e0 + 1),
  have : bit0 e0 + 1 + 1 = bit0 (e0 + 1), { simp [bit0], omega }, rw this at eq0,
  have eq1 : (L₀ (bit0 (e0 + 1))).length < (L₀ (bit0 (e0 + 1) + 1)).length,
    from L₀_length (e0 + 1), omega,
end

theorem L₁_length_lt (e) :
  e < (L₁ (bit1 e + 1)).length :=
begin
  induction e with e0 ih,
  { exact pos_of_gt (L₁_length 0) }, 
  have : bit1 e0 + 1 ≤ bit1 e0.succ, { simp [bit1, bit0], omega },
  have eq0 : (L₁ (bit1 e0 + 1)).length ≤ (L₁ (bit1 e0.succ)).length,
    from list.length_le_of_infix (list.infix_of_suffix $ initial_suffix₁ this),
  have eq1 : (L₁ (bit1 (e0 + 1))).length < (L₁ (bit1 (e0 + 1) + 1)).length,
    from L₁_length (e0 + 1), omega,
end


theorem L₀_fis : fis L₀ := λ s, suffix_initial (L₀_suffix s)

theorem L₁_fis : fis L₁ := λ s, suffix_initial (L₁_suffix s)

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

lemma zeroprime_computable₀ : I₀ ≤ₜ ∅′ :=
classical_iff.mpr $
begin
  have L₀_length' : ∀ n, n < (L₀ (bit0 n + 1)).reverse.length, simp [L₀_length_lt],
  have eqn0 : pfun.lift (chr I₀) = (λ n, (L₀ (bit0 n + 1)).rnth n),
  { funext n,
    have eqn0 := list.nth_le_nth (L₀_length' n),
    have eqn1 := L₀_subseq (bit0 n + 1) _ _ eqn0, simp at eqn1,
    unfold_coes,
    simp [pfun.lift, list.rnth, of_option, eqn0, eqn1] },
  simp [rcomputable], unfold_coes, rw eqn0,
  have := primrec.list_rnth.to_comp.to_rcomp.comp 
      ((L₀_0'computable.comp (primrec.nat_add.comp 
        primrec.nat_bit0 (primrec.const 1)).to_comp.to_rcomp).pair rcomputable.id),
  exact this.of_option
end

lemma zeroprime_computable₁ : I₁ ≤ₜ ∅′ :=
classical_iff.mpr $
begin
  have L₁_length' : ∀ n, n < (L₁ (bit1 n + 1)).reverse.length, simp [L₁_length_lt],
  have eqn0 : pfun.lift (chr I₁) = (λ n, (L₁ (bit1 n + 1)).rnth n),
  { funext n,
    have eqn0 := list.nth_le_nth (L₁_length' n),
    have eqn1 := L₁_subseq (bit1 n + 1) _ _ eqn0, simp at eqn1,
    unfold_coes,
    simp [pfun.lift, list.rnth, of_option, eqn0, eqn1] },
  simp [rcomputable], unfold_coes, rw eqn0,
  have := primrec.list_rnth.to_comp.to_rcomp.comp 
      ((L₁_0'computable.comp (primrec.nat_add.comp 
        primrec.nat_bit1 (primrec.const 1)).to_comp.to_rcomp).pair rcomputable.id),
  exact this.of_option
end

lemma requirement₀ (e) : ∃ w : ℕ,
  ¬(⟦e⟧ᵪ^(chr* I₁) w).dom ∨ !chr I₀ w ∈ (⟦e⟧ᵪ^(chr* I₁) w) :=
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
    have lmm1 : b ∈ (⟦e⟧ᵪ^(chr* I₁) (L₀ (2*e)).length),
    { rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩, apply hs, simp,
      have := L₁_subseq (2*e + 1), simp[nL₁, subseq] at this,
      exact (λ n c _, this n c) },
    simp[lmm0, lmm1] }
end

lemma requirement₁ (e) : ∃ w : ℕ,
  ¬(⟦e⟧ᵪ^(chr* I₀) w).dom ∨ !chr I₁ w ∈ (⟦e⟧ᵪ^(chr* I₀) w) :=
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
    have lmm1 : b ∈ (⟦e⟧ᵪ^(chr* I₀) (L₁ i).length),
    { rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩, apply hs, simp,
      have := L₀_subseq (i + 1), simp[nL₀, subseq] at this,
      exact (λ n c _, this n c) },
    simp[lmm0, lmm1] }
end

lemma incomparable₀ : I₀ ≰ₜ I₁ :=
begin
  assume h : I₀ ≤ₜ I₁,
  have l0 : ↑(chr I₀) partrec_in ↑(chr I₁) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧ᵪ^(chr* I₁) = ↑(chr I₀) := rpartrec.rpartrec_univ_iff_total.mp l0,
  rcases this with ⟨e, he⟩,
  have E : ∀ n, (chr I₀ n) ∈ (⟦e⟧ᵪ^(chr* I₁ ) n), simp[he],
  rcases requirement₀ e with ⟨w, hw⟩, cases hw,
  { have : (⟦e⟧ᵪ^(chr* I₁) w).dom, { rcases E w with ⟨h, _⟩, exact h },
    contradiction },
    have : chr I₀ w = !chr I₀ w := roption.mem_unique (E w) hw,
  show false, from bnot_ne _ this
end

lemma incomparable₁ : I₁ ≰ₜ I₀ :=
begin
  assume h : I₁ ≤ₜ I₀,
  have l0 : ↑(chr I₁) partrec_in ↑(chr I₀) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧ᵪ^(chr* I₀) = ↑(chr I₁) := rpartrec.rpartrec_univ_iff_total.mp l0,
  rcases this with ⟨e, he⟩,
  have E : ∀ n, (chr I₁ n) ∈ (⟦e⟧ᵪ^(chr* I₀ ) n), simp[he],
 rcases requirement₁ e with ⟨w, hw⟩, cases hw,
  { have : (⟦e⟧ᵪ^(chr* I₀) w).dom, { rcases E w with ⟨h, _⟩, exact h },
    contradiction },
    have : chr I₁ w = !chr I₁ w := roption.mem_unique (E w) hw,
  show false, from bnot_ne _ this
end

theorem Kleene_Post : ∃ I₀ I₁ : set ℕ, (I₀ ≤ₜ ∅′) ∧ (I₁ ≤ₜ ∅′) ∧ (I₀ ≰ₜ I₁) ∧ (I₁ ≰ₜ I₀) :=
⟨I₀, I₁, zeroprime_computable₀, zeroprime_computable₁, incomparable₀, incomparable₁⟩

end Kleene_Post

theorem Friedberg_Muchnik : ∃ (A B : set ℕ), re_pred A ∧ re_pred B ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end t_reducible