import reducibility computable_function fis

open encodable denumerable roption

local attribute [instance, priority 0] classical.prop_decidable
local attribute [simp] set.set_of_app_iff

lemma bnot_ne (b) : b ≠ !b := by cases b; simp

namespace t_reducible
open primrec

theorem extendable_suffix {l₀ n e} {A : ℕ → bool}
  (h : ∀ l : list bool, ¬(⟦e⟧ᵪ^(l ++ l₀).rnth n).dom) (hl₀ : l₀.rnth ⊆* (λ x, A x)) :
  ¬(⟦e⟧ᵪ^(λ x, some (A x)) n).dom := λ C,
begin
  rcases roption.dom_iff_mem.mp C with ⟨b, hb⟩,
  rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩,
  have := initial_subseq hl₀ s, rcases this with ⟨l, hl⟩,
  suffices : b ∈ (⟦e⟧ᵪ^((l ++ l₀).rnth) n),
  { rcases this with ⟨lmm, _⟩, exact h _ lmm },
  apply hs, simp, intros m c em hc,
  have : (initial_code (λ (x : ℕ), A x) s).rnth m = c, simp[em, hc],
  exact hl _ _ this
end

def O₀ := {x : ℕ × list bool × ℕ | ∃ l, (⟦x.1⟧ᵪ^(l ++ x.2.1).rnth x.2.2).dom}

def O₁ := {x : ℕ × list bool × ℕ | (⟦x.1⟧ᵪ^x.2.1.rnth x.2.2).dom}

theorem O₀_0'computable : O₀ ≤ₜ ∅′ :=
begin
  let f := (λ (x : ℕ × list bool × ℕ) l, ⟦x.1⟧ᵪ^(l ++ x.2.1).rnth x.2.2),
  have := (fst.comp fst).pair ((list_append.comp snd (fst.comp $ snd.comp fst)).pair
    (snd.comp $ snd.comp fst)),
  have : partrec₂ f := (rpartrec.eval_list_partrec ℕ bool).comp this.to_comp,
  have := domex_0'computable this,
  exact this
end

theorem O₁_0'computable : O₁ ≤ₜ ∅′ :=
dom_0'computable (rpartrec.eval_list_partrec ℕ bool)

namespace Kleene_Post

noncomputable def L : ℕ →. list bool × list bool
| 0     := some ([], [])
| (s+1) :=
  let e := s.div2 in
  match s.bodd with
  | ff := do σ ← L s,
    if (e, σ.2, σ.1.length) ∈ O₀
    then do l ← epsilon (chr $ λ l, (⟦e⟧ᵪ^(l ++ σ.2).rnth σ.1.length).dom),
            b ← (⟦e⟧ᵪ^((l ++ σ.2).rnth) σ.1.length),
            some (!b :: σ.1, l ++ σ.2)
    else some (ff :: σ.1, σ.2)
  | tt := do σ ← L s,
    if (e, σ.1, σ.2.length) ∈ O₀
    then do l ← epsilon (chr $ λ l, (⟦e⟧ᵪ^((l ++ σ.1).rnth) σ.2.length).dom),
            b ← (⟦e⟧ᵪ^((l ++ σ.1).rnth) σ.2.length),
            some (l ++ σ.1, !b :: σ.2)
    else some (σ.1, ff :: σ.2)
  end

lemma L_0'partrec'₀ :
  (λ (a : ℕ × list bool × list bool),
    epsilon (chr (λ l, (⟦a.fst.div2⟧ᵪ^((l ++ a.snd.fst).rnth) a.snd.snd.length).dom)) >>=
    λ l, (⟦a.1.div2⟧ᵪ^((l ++ a.2.1).rnth) a.2.2.length >>=
    λ b, some (l ++ a.2.1, !b :: a.2.2))) partrec_in chr. ∅′ :=
begin
  let p := (λ x : (ℕ × list bool × list bool) × list bool,
    chr O₁ (x.1.1.div2, x.2 ++ x.1.2.1, x.1.2.2.length)),
  have : ∀ a : ℕ × list bool × list bool,
    chr (λ l, (⟦a.1.div2⟧ᵪ^((l ++ a.2.1).rnth) a.2.2.length).dom) = λ l, p (a, l),
  { intros a, funext x, apply chr_ext.mpr, simp [O₁] }, simp [this],
  have lmm : (λ a, epsilon (λ x, p (a, x))) partrec_in chr. ∅′,
  { have := (nat_div2.comp $ fst.comp fst).pair 
      ((list_append.comp snd (fst.comp $ snd.comp fst)).pair 
      (list_length.comp $ snd.comp $ snd.comp fst)),
    have := (classical_iff.mp O₁_0'computable).comp this.to_comp.to_rcomp,
    exact (rpartrec.epsilon_rpartrec p).trans this },
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
  have := lmm.bind lmm1.to_rpart, simp [g] at this,
  exact this
end

lemma L_0'partrec'₁ :
  (λ (a : ℕ × list bool × list bool),
    epsilon (chr (λ l, (⟦a.fst.div2⟧ᵪ^((l ++ a.snd.snd).rnth) a.snd.fst.length).dom)) >>=
    λ l, ⟦a.1.div2⟧ᵪ^((l ++ a.2.2).rnth) a.2.1.length >>=
    λ b, some (!b :: a.2.1, l ++ a.2.2)) partrec_in chr. ∅′ :=
begin
  let p := (λ x : (ℕ × list bool × list bool) × list bool,
    chr O₁ (x.1.1.div2, x.2 ++ x.1.2.2, x.1.2.1.length)),
  have : ∀ a : ℕ × list bool × list bool,
    chr (λ l, (⟦a.1.div2⟧ᵪ^((l ++ a.2.2).rnth) a.2.1.length).dom) = λ l, p (a, l),
  { intros a, funext x, apply chr_ext.mpr, simp [O₁] },
  have lmm : (λ a, epsilon (λ x, p (a, x))) partrec_in chr. ∅′,
  { have := (nat_div2.comp $ fst.comp fst).pair 
      ((list_append.comp snd (snd.comp $ snd.comp fst)).pair 
      (list_length.comp $ fst.comp $ snd.comp fst)),
    have := (classical_iff.mp O₁_0'computable).comp this.to_comp.to_rcomp,
    exact (rpartrec.epsilon_rpartrec p).trans this },
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
  have := lmm.bind lmm1.to_rpart, simp [g] at this,
  exact this
end

lemma L_0'partrec : L partrec_in (chr. ∅′) :=
begin
  let h : ℕ × ℕ × (list bool × list bool) →. list bool × list bool := λ x,
    let s := x.2.1,
        σ := x.2.2,
        e := s.div2 in
    cond s.bodd
      (cond (chr O₀ (e, σ.1, σ.2.length))
        (do l ← epsilon (chr $ λ l, (⟦e⟧ᵪ^((l ++ σ.1).rnth) σ.2.length).dom),
            b ← (⟦e⟧ᵪ^((l ++ σ.1).rnth) σ.2.length),
            some (l ++ σ.1, !b :: σ.2))
        (some (σ.1, ff :: σ.2)))    
      (cond (chr O₀ (e, σ.2, σ.1.length))
        (do l ← epsilon (chr $ λ l, (⟦e⟧ᵪ^((l ++ σ.2).rnth) σ.1.length).dom),
            b ← (⟦e⟧ᵪ^((l ++ σ.2).rnth) σ.1.length),
            some (!b :: σ.1, l ++ σ.2))
        (some (ff :: σ.1, σ.2))),
  have : h partrec_in (chr. ∅′),
  { simp [h], apply rpartrec.cond,
    { exact (primrec.nat_bodd.comp $ primrec.fst.comp primrec.snd).to_comp.to_rcomp },
    { apply rpartrec.cond,
      { have := (primrec.nat_div2.comp primrec.fst).pair ((primrec.fst.comp primrec.snd).pair 
          (primrec.list_length.comp $ primrec.snd.comp primrec.snd)),
        have := (classical_iff.mp O₀_0'computable).comp
          (this.comp primrec.snd).to_comp.to_rcomp, 
        exact this },
      { exact L_0'partrec'₀.comp rcomputable.snd }, 
      { have := (fst.comp $ snd.comp snd).pair 
          (list_cons.comp (const ff) (snd.comp $ snd.comp snd)),
        exact this.to_comp.to_rcomp } },
    { apply rpartrec.cond,
      { have := (primrec.nat_div2.comp primrec.fst).pair ((primrec.snd.comp primrec.snd).pair 
          (primrec.list_length.comp $ primrec.fst.comp primrec.snd)),
        have := (classical_iff.mp O₀_0'computable).comp
          (this.comp primrec.snd).to_comp.to_rcomp,
        exact this },
      { exact L_0'partrec'₁.comp rcomputable.snd },
      { have := (list_cons.comp (const ff) (fst.comp $ snd.comp snd)).pair
          (snd.comp $ snd.comp snd),
        exact this.to_comp.to_rcomp } } },
  have := rpartrec.nat_elim (rcomputable.id)
    (rcomputable.const (([], []) : list bool × list bool)) this,
  exact (this.of_eq $ λ s, by 
  { simp, induction s with s0 ih; simp [L],
    cases C : s0.bodd; simp [C, L, h] at ih ⊢; rw ih; congr; funext; simp [C, O₀, cond_if_eq] })
end

lemma I_defined : ∀ s, (L s).dom 
| 0     := by simp[L]
| (s+1) :=
    let e := s.div2 in
    have IH : _ := I_defined s,
    begin
      simp[L], cases M : s.bodd; simp[M, L],
      { refine ⟨IH, _⟩,
        by_cases C : (s.div2, ((L s).get IH).snd, ((L s).get IH).fst.length) ∈ O₀;
        simp [C], simp [O₀, set.set_of_app_iff] at C, refine ⟨C, _⟩,
        have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦s.div2⟧ᵪ^((l ++ ((L s).get IH).2).rnth) ((L s).get IH).1.length).dom),
        { simp[←roption.dom_iff_mem], exact C },
        rcases this with ⟨l, hl⟩,
        have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
        rcases hb with ⟨b, hb⟩,
        simp[roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb, roption.some] },    
      { refine ⟨IH, _⟩,
        by_cases C : (s.div2, ((L s).get IH).1, ((L s).get IH).2.length) ∈ O₀;
        simp [C], simp [O₀, set.set_of_app_iff] at C, refine ⟨C, _⟩,
        have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦s.div2⟧ᵪ^((l ++ ((L s).get IH).1).rnth) ((L s).get IH).2.length).dom),
        { simp[←roption.dom_iff_mem], exact C },
        rcases this with ⟨l, hl⟩,
        have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
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
  have : (λ (a : ℕ), (L a).get _) computable_in chr. ∅′ := rpartrec.trans this L_0'partrec,
  exact rcomputable.fst.comp this,
end

lemma L₁_0'computable : L₁ computable_in chr. ∅′ :=
begin
  have := (rcomputable.total_computable I_defined),
  have : (λ (a : ℕ), (L a).get _) computable_in chr. ∅′ := rpartrec.trans this L_0'partrec,
  exact rcomputable.snd.comp this,
end

lemma L₀_length (e) :
  (L₀ (bit0 e)).length < (L₀ (bit0 e + 1)).length :=
begin
  simp[fis, L₀, L], simp [L, show ∀ s, L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { by_cases C : (e, L₁ (bit0 e), (L₀ (bit0 e)).length) ∈ O₀; simp [C],
    have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦e⟧ᵪ^((l ++ L₁ (bit0 e)).rnth) (L₀ (bit0 e)).length).dom),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb ] }
end

lemma L₁_length (e) :
  (L₁ (bit1 e)).length < (L₁ (bit1 e + 1)).length :=
begin
  simp[fis, L₁, L], simp [L, show ∀ s, L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { by_cases C : (e, L₀ (bit1 e), (L₁ (bit1 e)).length) ∈ O₀; simp [C],
    have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦e⟧ᵪ^((l ++ L₀ (bit1 e)).rnth) (L₁ (bit1 e)).length).dom),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb ] }
end

lemma L₀_fiss : fiss L₀ := λ s,
begin
  show L₀ s <:+ L₀ (s + 1),
  let e := s.div2,
  simp[fis, L₀, L], cases M : s.bodd; simp [M, L, show L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { by_cases C : (s.div2, L₁ s, (L₀ s).length) ∈ O₀; simp [C],
    have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦s.div2⟧ᵪ^((l ++ L₁ s).rnth) (L₀ s).length).dom),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },  
  { by_cases C : (s.div2, L₀ s, (L₁ s).length) ∈ O₀; simp [C],
    have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦s.div2⟧ᵪ^((l ++ L₀ s).rnth) (L₁ s).length).dom),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] }
end

lemma L₁_fiss : fiss L₁ := λ s,
begin
  show L₁ s <:+ L₁ (s + 1),
  let e := s.div2,
  simp[fis, L₁, L], cases M : s.bodd; simp [M, L, show L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { by_cases C : (s.div2, L₁ s, (L₀ s).length) ∈ O₀; simp [C],
    have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦s.div2⟧ᵪ^((l ++ L₁ s).rnth) (L₀ s).length).dom),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },  
  { by_cases C : (s.div2, L₀ s, (L₁ s).length) ∈ O₀; simp [C],
    have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦s.div2⟧ᵪ^((l ++ L₀ s).rnth) (L₁ s).length).dom),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] }
end

lemma L₀_full : full L₀ := λ n, ⟨bit0 n + 1, 
begin
  show n < (L₀ (bit0 n + 1)).length,
  induction n with n0 ih,
  exact L₀_length 0, 
  have eq0 : (L₀ (bit0 n0 + 1)).length ≤ (L₀ (bit0 n0 + 1 + 1)).length,
    from list.length_le_of_infix (list.infix_of_suffix $ L₀_fiss $ bit0 n0 + 1),
  have : bit0 n0 + 1 + 1 = bit0 (n0 + 1), { simp [bit0], omega }, rw this at eq0,
  have eq1 : (L₀ (bit0 (n0 + 1))).length < (L₀ (bit0 (n0 + 1) + 1)).length,
    from L₀_length (n0 + 1), omega,  
end⟩

lemma L₁_full : full L₁ := λ n, ⟨bit1 n + 1,
begin
  show n < (L₁ (bit1 n + 1)).length,
  have initial_suffix₁ : ∀ {s t}, s ≤ t → L₁ s <:+ L₁ t,
  from relation_path_le (<:+) list.suffix_refl (λ a b c, list.is_suffix.trans) L₁_fiss,
  induction n with n0 ih,
  { exact pos_of_gt (L₁_length 0) }, 
  have : bit1 n0 + 1 ≤ bit1 n0.succ, { simp [bit1, bit0], omega },
  have eq0 : (L₁ (bit1 n0 + 1)).length ≤ (L₁ (bit1 n0.succ)).length,
    from list.length_le_of_infix (list.infix_of_suffix $ initial_suffix₁ this),
  have eq1 : (L₁ (bit1 (n0 + 1))).length < (L₁ (bit1 (n0 + 1) + 1)).length,
    from L₁_length (n0 + 1), omega
end⟩

lemma I₀_0'computable : I₀ ≤ₜ ∅′ :=
classical_iff.mpr $ (L₀_fiss.limit_fullfiss_computable L₀_full).trans L₀_0'computable

lemma I₁_0'computable : I₁ ≤ₜ ∅′ :=
classical_iff.mpr $ (L₁_fiss.limit_fullfiss_computable L₁_full).trans L₁_0'computable

lemma requirement₀ (e) : ∃ w : ℕ,
  !chr I₀ w ∈ ⟦e⟧ᵪ^(chr* I₁) w ∨ ¬(⟦e⟧ᵪ^(chr* I₁) w).dom :=
begin
  let i := 2*e,
  let w := (L₀ i).length,
  use w,
  by_cases C : (e, L₁ i, w) ∈ O₀,
  { left,
    show !chr I₀ w ∈ ⟦e⟧ᵪ^(chr* I₁) w,
    have : ∃ l, l ∈ epsilon (chr (λ l, (⟦e⟧ᵪ^((l ++ L₁ i).rnth) w).dom)),
    { simp[←roption.dom_iff_mem] at C ⊢, exact C },
    rcases this with ⟨l, hl⟩,
    have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    have : L₀ (i + 1) = !b :: L₀ i ∧ L₁ (i + 1) = l ++ L₁ i,
    { simp [L₀, L₁, L, show i.div2 = e, by simp[nat.div2_val]], 
      simp [L, show L i = some (L₀ i, L₁ i), by simp[L₀, L₁], C,
        roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },
    rcases this with ⟨nL₀, nL₁⟩,
    have lmm : chr I₀ w = !b,
    { have := L₀_fiss.fiss_subseq_limit (i + 1) (w) (!b),
      simp [nL₀, list.rnth] at this, apply this,
      rw (show w = (L₀ i).reverse.length, by simp),
      simp only [list.nth_concat_length] },
    have lmm1 : b ∈ ⟦e⟧ᵪ^(chr* I₁) w,
    { rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩, apply hs, simp,
      have := L₁_fiss.fiss_subseq_limit (i + 1), simp[nL₁, subseq] at this,
      exact (λ n c _, this n c) },
    simp[lmm, lmm1] },
  { right, simp [O₀] at C,
    have : (L₁ i).rnth ⊆* chr* I₁, from L₁_fiss.fiss_subseq_limit _,
    exact extendable_suffix C this }
end

lemma requirement₁ (e) : ∃ w : ℕ,
  !chr I₁ w ∈ ⟦e⟧ᵪ^(chr* I₀) w ∨ ¬(⟦e⟧ᵪ^(chr* I₀) w).dom :=
begin
  let i := bit1 e,
  let w := (L₁ i).length,
  use w,
  by_cases C : (e, L₀ i, w) ∈ O₀,
  { left, show !chr I₁ w ∈ ⟦e⟧ᵪ^(chr* I₀) w,
    have : ∃ l, l ∈ epsilon (chr $ λ l, (⟦e⟧ᵪ^((l ++ L₀ i).rnth) w).dom),
    { simp[←roption.dom_iff_mem] at C ⊢, exact C },
    rcases this with ⟨l, hl⟩,
    have hb := epsilon_witness hl, simp only [chr_iff, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    have : L₀ (i + 1) = l ++ L₀ i ∧ L₁ (i + 1) = !b :: L₁ i,
    { simp [L₀, L₁, L, show i.div2 = e, by simp[i]], 
      simp [L, show L i = some (L₀ i, L₁ i), by simp[L₀, L₁], C,
        roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },
    rcases this with ⟨nL₀, nL₁⟩,
    have lmm : chr I₁ w = !b,
    { have := L₁_fiss.fiss_subseq_limit (i + 1) (w) (!b),
      simp [nL₁, list.rnth] at this, apply this,
      rw (show w = (L₁ i).reverse.length, by simp),
      simp only [list.nth_concat_length] },
    have lmm1 : b ∈ ⟦e⟧ᵪ^(chr* I₀) w,
    { rcases rpartrec.eval_inclusion hb with ⟨s, hs⟩, apply hs, simp,
      have := L₀_fiss.fiss_subseq_limit (i + 1), simp[nL₀, subseq] at this,
      exact (λ n c _, this n c) },
    simp[lmm, lmm1] },
  { right, simp [O₀] at C,
    have : (L₀ i).rnth ⊆* chr* I₀, from L₀_fiss.fiss_subseq_limit _,
    exact extendable_suffix C this }
end

lemma incomparable₀ : ¬I₀ ≤ₜ I₁ :=
begin
  assume hyp : I₀ ≤ₜ I₁,
  have : ∃ e, ⟦e⟧ᵪ^(chr* I₁) = chr I₀ :=
    rpartrec.rpartrec_univ_iff_total.mp (classical_iff.mp hyp),
  rcases this with ⟨e, lmm_e⟩,
  have lmm : ∀ n, (chr I₀ n) ∈ (⟦e⟧ᵪ^(chr* I₁) n), simp[lmm_e],
  rcases requirement₀ e with ⟨w, lmm_w⟩, cases lmm_w,
  { have : chr I₀ w = !chr I₀ w := roption.mem_unique (lmm w) lmm_w,
    show false, from bnot_ne _ this },
  { have : (⟦e⟧ᵪ^(chr* I₁) w).dom, { rcases lmm w with ⟨h, _⟩, exact h },
    contradiction }
end

lemma incomparable₁ : ¬I₁ ≤ₜ I₀ :=
begin
  assume hyp : I₁ ≤ₜ I₀,
  have : ∃ e, ⟦e⟧ᵪ^(chr* I₀) = chr I₁ :=
    rpartrec.rpartrec_univ_iff_total.mp (classical_iff.mp hyp),
  rcases this with ⟨e, lmm_e⟩,
  have lmm : ∀ n, (chr I₁ n) ∈ (⟦e⟧ᵪ^(chr* I₀) n), simp[lmm_e],
  rcases requirement₁ e with ⟨w, lmm_w⟩, cases lmm_w,
  { have : chr I₁ w = !chr I₁ w := roption.mem_unique (lmm w) lmm_w,
    show false, from bnot_ne _ this },
  { have : (⟦e⟧ᵪ^(chr* I₀) w).dom, { rcases lmm w with ⟨h, _⟩, exact h },
    contradiction }
end

theorem Kleene_Post : ∃ I₀ I₁ : set ℕ,
  I₀ ≤ₜ ∅′ ∧ I₁ ≤ₜ ∅′ ∧ ¬I₀ ≤ₜ I₁ ∧ ¬I₁ ≤ₜ I₀ :=
⟨I₀, I₁, I₀_0'computable, I₁_0'computable, incomparable₀, incomparable₁⟩

theorem Kleene_Post' : ∃ d₀ d₁ : turing_degree,
  d₀ ≤ 0⁺ ∧ d₁ ≤ 0⁺ ∧ ¬d₀ ≤ d₁ ∧ ¬d₁ ≤ d₀ :=
⟨turing_degree.of I₀, turing_degree.of I₁, by { simp [has_zero.zero],
 exact ⟨I₀_0'computable, I₁_0'computable, incomparable₀, incomparable₁⟩}⟩

theorem Friedberg_Muchnik' : ∃ d₀ d₁ : turing_degree,
  d₀ ∈ 𝓡 ∧ d₁ ∈ 𝓡 ∧ ¬d₀ ≤ d₁ ∧ ¬d₁ ≤ d₀ :=
by sorry

end Kleene_Post

end t_reducible