import reducibility computable_function

open encodable denumerable roption t_reducible

local attribute [simp] set.set_of_app_iff

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

namespace fis

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

def subseq (A B : ℕ → option bool) := ∀ n b, A n = some b → B n = some b

infix ` ⊆. `:50 := subseq

-- finite initial segments
def fis (L : ℕ → list bool) := ∀ s, L s ≼ L (s + 1)

def sfis (L : ℕ → list bool) := ∀ s, L s <:+ L (s + 1)

theorem sfis.fis {L : ℕ → list bool} (h : sfis L) : fis L :=
λ s, suffix_initial (h s)

def total (L : ℕ → list bool) := ∀ n, ∃ s, n < (L s).length

def limit (L : ℕ → list bool) := {n | ∃ s, (L s).rnth n = tt}

theorem limit_jumpcomputabile {L : ℕ → list bool} {A : set ℕ} (cL : L computable_in chr. A) :
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
  have : {x | ∃ y, (f (x, y)).dom} ≤ₜ A′ := t_reducible.domex_jumpcomputable lmm0,
  rw eqn0, exact this
end

theorem initial_trans {l₀ l₁ l₂ : list bool} : l₀ ≼ l₁ → l₁ ≼ l₂ → l₀ ≼ l₂ :=
 λ h01 h12 _ e, h12 _ (h01 _ e)

theorem fis_le {L : ℕ → list bool} (h : fis L) :
  ∀ {s t}, s ≤ t → L s ≼ L t := 
relation_path_le (≼) (by simp) (λ a b c, initial_trans) h

theorem sfis_le {L : ℕ → list bool} (h : sfis L) :
  ∀ {s t}, s ≤ t → L s <:+ L t := 
relation_path_le (<:+) list.suffix_refl (λ a b c, list.is_suffix.trans) h

theorem fis_limit_eq {L : ℕ → list bool} (F : fis L) (m) :
  limit L = limit (λ x, L (x + m)) := funext $ λ n,
begin
  simp[limit, set.set_of_app_iff], split,
  { rintros ⟨s, hs⟩, have : s ≤ m ∨ m < s, from le_or_lt s m,
    cases this,
    refine ⟨0, _⟩, simp,
    exact fis_le F this _ hs,
    refine ⟨s-m, _⟩,  have : s - m + m = s, omega, simp [this],
    exact hs },
  { rintros ⟨s, hs⟩, refine ⟨s+m, hs⟩ }
end

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

lemma sfis_subseq_limit {L} (F : sfis L) (s) : (L s).rnth ⊆. chr* limit L :=
subseq_limit (L s).rnth F.fis ⟨s, λ u eu, suffix_subseq (sfis_le F eu)⟩

theorem limit_totalsfis_computable {L} (F : sfis L) (T : total L) : 
  chr (limit L) computable_in (L : ℕ →. list bool) :=
begin
  let f : ℕ →. bool := (λ n, nat.rfind_opt (λ s, (L s).rnth n)),
  have eqn0 : f = pfun.lift (chr $ limit L),
  { funext n, simp [f, roption.eq_some_iff],
    rcases T n with ⟨s, hs⟩, have hs' : n < (L s).reverse.length, simp [hs],
    have eqnn : (L s).rnth n = some ((L s).reverse.nth_le n hs'), from list.nth_le_nth hs',
    have eqn0 : chr (limit L) n = (L s).reverse.nth_le n hs',
    { have := sfis_subseq_limit F s _ _ eqnn, simp at this, exact this },
    have mono : ∀ a s u, s ≤ u → a ∈ ((L s).rnth n) → a ∈ ((L u).rnth n),
    from λ a s u e h, suffix_subseq (sfis_le F e) n a h, 
    have : (L s).reverse.nth_le n hs' ∈ nat.rfind_opt (λ (s : ℕ), (L s).rnth n), 
    from (nat.rfind_opt_mono mono).mpr ⟨s, eqnn⟩,      
    simp [eqn0, this] },
  have : f partrec_in ↑L,
  { have := primrec.list_rnth.to_comp.to_rcomp.comp 
      (((rcomputable.refl_in L).comp rcomputable.snd).pair rcomputable.fst), simp at this,
    have := rpartrec.rfind_opt this,
    exact this },
  rw eqn0 at this,
  exact this
end

end fis