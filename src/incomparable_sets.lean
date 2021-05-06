import reducibility computable_function

open encodable denumerable roption



lemma list.append_nth_some {α} {l₀ : list α} {n a} (h : l₀.nth n = some a) (l₁) :
  (l₀ ++ l₁).nth n = some a :=
by { have := list.nth_eq_some.mp h, rcases this with ⟨en, _⟩,
     exact eq.trans (list.nth_append en) h, }

lemma list.drop_nth {α} : ∀ (l : list α) (k n), (l.drop k).nth n = l.nth (n + k)
| []        _       _ := by simp [list.drop]
| (l :: ls) 0       _ := by simp [list.drop]
| (l :: ls) (k + 1) n := 
    by { simp [list.drop], have := list.drop_nth ls k n, simp [this], exact rfl }

inductive list.is_initial {α} : list α → list α → Prop
| refl {l}   : list.is_initial l l
| cons {l₀ l₁ a} : list.is_initial l₀ l₁ → list.is_initial l₀ (a :: l₁)
| trans {l₀ l₁ l₂} : list.is_initial l₀ l₁ → list.is_initial l₁ l₂ → list.is_initial l₀ l₂

namespace t_reducible


theorem gfeg {α} (l₀ l₁ : list α) :
  list.is_initial l₀ l₁ ↔ (∀ n a, l₀.rnth n = some a → l₁.rnth n = some a) :=
begin

end

def list.initial {α} (l₀ l₁ : list α) := ∀ n a, l₀.rnth n = some a → l₁.rnth n = some a
infix ` ≺ `:50 := list.initial

@[simp] theorem initial_refl {α} (l : list α) : l ≺ l :=
by simp[list.initial]

@[simp] theorem initial_append {α} (l l₀ : list α) : l ≺ l₀ ++ l := λ n b h,
by { simp[list.initial, list.rnth] at h ⊢, simp only [list.append_nth_some h] } 

@[simp] theorem initial_cons {α} (a) (l : list α) : l ≺ a :: l := λ n b h,
by { simp[list.initial, list.rnth] at h ⊢, simp only [list.append_nth_some h] } 

def limit (L : ℕ → list bool) := {n | ∃ s, (L s).rnth n = tt}

-- finite initial segments
def fis (L : ℕ → list bool) := ∀ s, L s ≺ L (s + 1)

def total {α} (L : ℕ → list α) := ∀ n, ∃ s, n < (L s).length

lemma total_limit_dom {α} {L : ℕ → list α} (T : total L) (n) : ∃ s a, (L s).rnth n = some a :=
by { rcases T n with ⟨s, hs⟩, refine ⟨s, (L s).reverse.nth_le _ _, list.nth_le_nth _⟩, simp, exact hs }

theorem initial_trans {α} {l₀ l₁ l₂ : list α} : l₀ ≺ l₁ → l₁ ≺ l₂ → l₀ ≺ l₂ :=
 λ h01 h12 _ _ e, h12 _ _ (h01 _ _ e)

theorem initial_le {L : ℕ → list bool} (h : fis L) :
  ∀ {s t}, s ≤ t → L s ≺ L t :=
begin
  have l0 : ∀ s t, L s ≺ L (s + t),
  { intros s t, induction t with s0 ih generalizing s, simp[list.initial],
    simp[show s + s0.succ = (s + s0) + 1, from nat.add_succ _ _],
    exact initial_trans (ih _) (h _) },
  intros s t e,
  have : t = s + (t - s), omega,
  rw this, exact l0 _ _,
end 

theorem initial_limit {L : ℕ → list bool} (h : fis L)
  {s n b} : (L s).rnth n = some b → chr (limit L) n = b := λ eb,
begin
  simp[limit], unfold_coes, cases b; simp[set.set_of_app_iff],
    { intros u c, have : s ≤ u ∨ u ≤ s, from le_total s u, cases this,
    have := initial_le h this _ _ eb, simp[c] at this, exact this,
    have := initial_le h this _ _ c, simp[eb] at this, exact this },
  refine ⟨s, eb⟩
end

lemma chr_limit_iff0 {L : ℕ → list bool} (H : fis L) (n b) :
  chr (limit L) n = b ↔ ∀ s, (L s).length ≤ n ∨ (L s).rnth n = b :=
begin
  simp [limit,list.rnth, set.set_of_app_iff], split, 
end

lemma chr_limit_fis1 {L : ℕ → list bool} (F : fis L) (n b) :
  (∃ s, (L s).rnth n = some b) → chr (limit L) n = b :=
begin
  cases b; simp[limit, set.set_of_app_iff],
  { unfold_coes, intros s h u c,
    have e : u ≤ s ∨ s ≤ u, exact le_total _ _,
    cases e,
    { have := initial_le F e _ _ c, simp [h] at this, exact this },
    { have := initial_le F e _ _ h, simp [c] at this, exact this } },
  { intros s h, use s, exact h }
end

lemma chr_limit_ff {L : ℕ → list bool} (n) :
  chr (limit L) n = ff ↔ ∀ s, (L s).length ≤ n ∨ (L s).rnth n = ff :=
begin
  simp [limit,list.rnth, set.set_of_app_iff], split, 
  { intros h s, have : (L s).length ≤ n ∨ n < (L s).reverse.length, simp, exact le_or_lt _ _,
    cases this, { left, exact this },
    { right, cases e : (L s).reverse.nth_le n this, 
      simp [list.nth_le_nth this, e], refl,
      exfalso, have := list.nth_le_nth this, simp[e] at this, exact h _ this } },
  { intros h s c, cases h s with hs hs,
    { have := list.nth_len_le (show (L s).reverse.length ≤ n, by simp [hs]),
      unfold_coes at c, simp [c] at this, exact this },
    { unfold_coes at hs c, simp [c] at hs, exact hs } }
end

lemma chr_limit_tt {L : ℕ → list bool} (H : fis L) {n} :
  chr (limit L) n = tt → ∀ s, n < (L s).length → (L s).rnth n = tt := λ h s hs,
begin
  simp [limit,list.rnth, set.set_of_app_iff] at h ⊢, 
  rcases h with ⟨u, hu⟩,
  have e : u ≤ s ∨ s ≤ u, exact le_total _ _,
  cases e,
  { exact initial_le H e _ _ hu },
  { have hs' : n < (L s).reverse.length, simp [hs],
    cases e0 : (L s).reverse.nth_le n hs',
    { exfalso, have : (L u).reverse.nth n = ff, 
      { have := list.nth_le_nth hs', simp [e0] at this, exact initial_le H e _ _ this },
      unfold_coes at hu this, simp[hu] at this, exact this },
    {  simp [list.nth_le_nth hs', e0], refl } }
end

lemma initial_extendable {L : ℕ → list bool} (H : fis L) (s u) :
  ∃ l₀, initial_code (chr (limit L)) s ≺ l₀ ++ L u :=
begin
  refine ⟨((initial_code (chr (limit L)) s).reverse.drop (L u).length).reverse, _⟩,
  simp[list.initial, list.rnth], intros m c ec,
  have := initial_code_some ec, 
  have em : m < (L u).reverse.length ∨ (L u).reverse.length ≤ m, exact lt_or_ge _ _, 
  cases em,
  { simp[list.nth_append em], cases c,
    { have clff := (chr_limit_ff _).mp this u,
      cases clff, exfalso, simp at em, exact nat.lt_le_antisymm em clff,
      exact clff },
    { simp at em, exact chr_limit_tt H this _ em } },
  { simp [list.nth_append_right em], have : m - (L u).length + (L u).length = m, { simp at em, omega },
    simp [list.drop_nth, this], exact ec }
end

theorem oracle_initial_limit {L : ℕ → list bool} (H : fis L)
  {e s} {n : ℕ} {b : bool} :
  b ∈ (⟦e⟧^(L s).rnth n : roption bool) → 
  b ∈ (⟦e⟧^(chr* (limit L)) n : roption bool) := λ hs,
by { have := rpartrec.eval_inclusion hs, rcases this with ⟨u, hu⟩,
     apply hu, simp, exact λ _ _ _ e, initial_limit H e }

theorem oracle_initial_limit_dom {L : ℕ → list bool} (H : fis L)
  {e s} {n : ℕ} {b : bool} :
  (⟦e⟧^(L s).rnth n : roption bool).dom → 
  (⟦e⟧^(chr* (limit L)) n : roption bool).dom := λ hs,
by { have := roption.dom_iff_mem.mp hs, rcases this with ⟨b, hb⟩,
     have := oracle_initial_limit H hb, rcases this with ⟨h, _⟩,
     exact h }

theorem oracle_initial_limit_dom_neg {L : ℕ → list bool} (H : fis L)
  {e} {n : ℕ} {b : bool} :
  (∃ u, ∀ s, u < s → ¬(⟦e⟧^(L s).rnth n : roption bool).dom) → 
  ¬(⟦e⟧^(chr* (limit L)) n : roption bool).dom := 

theorem oracle_limit_extendable {L : ℕ → list bool} (H : fis L)
  {e} {n : ℕ} {b : bool} :
  b ∈ (⟦e⟧^(chr* (limit L)) n : roption bool) →
  ∀ s, ∃ l₀, b ∈ (⟦e⟧^(l₀ ++ L s).rnth n : roption bool) := λ hlim s,
begin
  have := rpartrec.eval_inclusion hlim, rcases this with ⟨u, hu⟩, simp at hu,
  have := initial_extendable H u s, rcases this with ⟨l, hl⟩,
  refine ⟨l, _⟩,
  apply hu, intros  m c em ec,
  have : (initial_code (chr (limit L)) u).rnth m = c, simp [em, ec],
  exact hl _ _ this  
end

namespace Kleene_Post

def extendable (l₀ l : list bool) (n e : ℕ) := (⟦e⟧^((l ++ l₀).rnth) n : roption bool).dom

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
| (s+1) :=
  let e := s.div2 in
  match s.bodd with
  | tt := do
    σ ← L s,
    cond (chr {e | ∃ l, extendable σ.2 l σ.1.length e} e)
      (do l ← ε_operator (chr $ λ l, extendable σ.2 l σ.1.length e),
          b ← (⟦e⟧^((l ++ σ.2).rnth) σ.1.length : roption bool),
          some (!b :: σ.1, l ++ σ.2))
      (some (ff :: σ.1, σ.2))
  | ff := do
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
      cases C : chr {i | ∃ l, extendable ((L s).get IH).fst l ((L s).get IH).snd.length i} e;
      simp [C], simp [set.set_of_app_iff] at C, refine ⟨C, _⟩,
      have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable ((L s).get IH).fst l ((L s).get IH).snd.length e),
      { simp[←roption.dom_iff_mem], exact C },
      rcases this with ⟨l, hl⟩,
      have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
      rcases hb with ⟨b, hb⟩,
      simp[roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb, roption.some] },
    { refine ⟨IH, _⟩,
      cases C : chr {i | ∃ l, extendable ((L s).get IH).snd l ((L s).get IH).fst.length i} e;
      simp [C], simp [set.set_of_app_iff] at C, refine ⟨C, _⟩,
      have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable ((L s).get IH).2 l ((L s).get IH).1.length e),
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

theorem L₀_fis :
  fis L₀ := λ s,
begin
  let e := s.div2,
  simp[fis, L₀, L], cases M : s.bodd; simp [M, L, show L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { cases C : chr {i | ∃ l, extendable (L₀ s) l (L₁ s).length i} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₀ s) l (L₁ s).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },
  { cases C : chr {e | ∃ l, extendable (L₁ s) l (L₀ s).length e} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₁ s) l (L₀ s).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] }
end

theorem L₁_fis :
  fis L₁ := λ s,
begin
  let e := s.div2,
  simp[fis, L₁, L], cases M : s.bodd; simp [M, L, show L s = some (L₀ s, L₁ s), by simp[L₀, L₁]],
  { cases C : chr {i | ∃ l, extendable (L₀ s) l (L₁ s).length i} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₀ s) l (L₁ s).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] },
  { cases C : chr {i | ∃ l, extendable (L₁ s) l (L₀ s).length i} e; simp [C],
    simp [set.set_of_app_iff] at C,
    have : ∃ l, l ∈ ε_operator (chr $ λ l, extendable (L₁ s) l (L₀ s).length e),
    { simp[←roption.dom_iff_mem], exact C },
    rcases this with ⟨l, hl⟩,
    have hb := ε_witness hl, simp only [chr_iff, extendable, roption.dom_iff_mem] at hb,
    rcases hb with ⟨b, hb⟩,
    simp [roption.eq_some_iff.mpr hl, roption.eq_some_iff.mpr hb] }
end

/--
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

lemma preservation₀ {e l b} (hl : l ∈ ε_operator (chr (λ l, extendable (L' $ bit1 e).2 l (L' $ bit1 e).1.length (bit1 $ e)))) :
  b ∈ (⟦e⟧^((l ++ (L' $ bit1 e).2).rnth) (L' $ bit1 e).1.length : roption bool) →
  b ∈ (⟦e⟧^(chr* I₁) (L' (bit1 e)).1.length : roption bool) := λ hb,
begin
  suffices : 
    b ∈ (⟦e⟧^(L' (bit1 e + 1)).2.rnth (L' $ bit1 e).1.length : roption bool),
  { exact oracle_initial_limit L₁_fis this },
  have hl' := ε_witness hl, simp at hl',
  have := rpartrec.eval_inclusion hb, rcases this with ⟨s, hs⟩,
  apply hs, intros x c ex ec,
  simp[L', L], simp[show L (bit1 e) = some (L' $ bit1 e), by simp[L']],
  have : chr {i | ∃ l, extendable (L' $ bit1 e).2 l (L' $ bit1 e).1.length i} (bit1 e) = tt,
  { simp [set.set_of_app_iff], exact ⟨l, hl'⟩ },
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
--/
theorem requirement₀ (e) (J₀ J₁ : set ℕ) : ∃ w : ℕ,
  ¬(⟦e⟧^(chr* J₀) w : roption bool).dom ∨ !chr J₀ w ∈ (⟦e⟧^(chr* J₁) w : roption bool) := by sorry

theorem requirement₁ (e) : ∃ w : ℕ,
  (⟦e⟧^(chr* I₀) w : roption bool).dom → !chr I₁ w ∈ (⟦e⟧^(chr* I₀) w : roption bool) := by sorry

lemma bnot_ne (b) : b ≠ !b := by cases b; simp

lemma incomparable₀ : I₀ ≰ₜ I₁ :=
begin
  assume h : I₀ ≤ₜ I₁,
  have l0 : ↑(chr I₀) partrec_in ↑(chr I₁) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧^(chr* I₁) = ↑(chr I₀) := rpartrec.rpartrec_univ_iff_total.mp l0,
  rcases this with ⟨e, he⟩,
  have E : ∀ n, (chr I₀ n) ∈ (⟦e⟧^(chr* I₁ ) n : roption bool), simp[he],
  rcases requirement₀ e with ⟨w, hw⟩,
  have : (⟦e⟧^(chr* I₁) w).dom, { rcases E w with ⟨h, _⟩, exact h },
  have : !chr I₀ w ∈ ⟦e⟧^(chr* I₁) w := hw this,
  have : chr I₀ w = !chr I₀ w := roption.mem_unique (E w) this,
  show false, from bnot_ne _ this
end

lemma incomparable₁ : I₁ ≰ₜ I₀ :=
begin
  assume h : I₁ ≤ₜ I₀,
  have l0 : ↑(chr I₁) partrec_in ↑(chr I₀) := classical_iff.mp h,
  have : ∃ e, ⟦e⟧^(chr* I₀) = ↑(chr I₁) := rpartrec.rpartrec_univ_iff_total.mp l0,
  rcases this with ⟨e, he⟩,
  have E : ∀ n, (chr I₁ n) ∈ (⟦e⟧^(chr* I₀ ) n : roption bool), simp[he],
  rcases requirement₁ e with ⟨w, hw⟩,
  have : (⟦e⟧^(chr* I₀) w).dom, { rcases E w with ⟨h, _⟩, exact h },
  have : !chr I₁ w ∈ ⟦e⟧^(chr* I₀) w := hw this,
  have : chr I₁ w = !chr I₁ w := roption.mem_unique (E w) this,
  show false, from bnot_ne _ this
end

theorem Kleene_Post : ∃ (A B : set ℕ), (A ≤ₜ ∅′) ∧ (B ≤ₜ ∅′) ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end Kleene_Post

theorem Friedberg_Muchnik : ∃ (A B : set ℕ), re_pred A ∧ re_pred B ∧ (A ≰ₜ B) ∧ (B ≰ₜ A) :=
by sorry

end t_reducible