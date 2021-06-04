import reducibility function

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

@[simp] lemma list.nth_length_none {α} : ∀ (l : list α), l.nth l.length = none :=
λ l, by cases l; simp

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

lemma relation_path_lt {α} {p : ℕ → α} (R : α → α → Prop)
  (t : ∀ a b c, R a b → R b c → R a c)
  (i : ∀ n, R (p (n+1)) (p n)) : 
  ∀ s t, s < t → R (p t) (p s) :=
begin
  have l0 : ∀ s t, R (p (s + t + 1)) (p s),
  { intros s t, induction t with s0 IH generalizing s, simp[i],
    simp[show s + s0.succ = (s + s0) + 1, from nat.add_succ _ _],
    exact t _ _ _ (i _) (IH _) },
  intros s t e,
  have : t = s + (t - s - 1) + 1, omega,
  rw this, exact l0 _ _,
end

namespace kb

class precede (α : Type*) :=
(prec : α → α → Prop)
(wf   : well_founded prec)

infix ` ≺ `:80 := precede.prec

variables {Λ : Type*}
variables [precede Λ]

lemma precede.induction {C : Λ → Prop} (a : Λ) (h : ∀ x, (∀ y, y ≺ x → C y) → C x) : C a :=
precede.wf.induction a h

lemma precede.minimal {C : Λ → Prop} (h : ∃ x, C x) : ∃ m, C m ∧ ∀ x, x ≺ m → ¬C x:=
begin
  suffices : ∀ a, C a → ∃ (m : Λ), C m ∧ ∀ (x : Λ), x ≺ m → ¬C x,
  { rcases h with ⟨a, ha⟩, refine this _ ha },
  intros a,
  apply precede.induction a,
  intros a IH Ca,
  by_cases C : ∃ b, b ≺ a ∧ C b,
  { rcases C with ⟨b, hyp_b, hyp_b1⟩, refine IH b hyp_b hyp_b1 },
  { simp at C, refine ⟨a, Ca, C⟩ }
end

lemma precede.enum_minimal {α} [inhabited α] (f : α → Λ) : ∃ m, ∀ n, ¬f n ≺ f m :=
begin
  let C := (λ x : Λ, ∃ n, f n = x),
  have := @precede.minimal _ _ C ⟨f (default α), ⟨(default α), rfl⟩⟩,
  simp[C] at this, rcases this with ⟨w, hyp_w⟩,
  refine ⟨w, λ n A, _⟩, have := hyp_w (f n) A,
  have := this n, simp at this, exact this
end

lemma precede.antirefl {a : Λ} : ¬a ≺ a :=
by { have := precede.enum_minimal (λ n : ℕ, a), simp at this, exact this }

inductive option.prec : option Λ → option Λ → Prop
| none {a} : option.prec (some a) none
| some {a b} : a ≺ b → option.prec (some a) (some b)

lemma option.prec.trans (trans : transitive (@precede.prec Λ _)) :
  transitive (@option.prec Λ _) :=
λ a b c ab bc,
begin
  cases ab with a a b ab',
  { cases bc },
  { cases bc with _ _ c bc', exact option.prec.none,
    exact option.prec.some (trans ab' bc'), }
end

lemma option.prec.wf : well_founded (@option.prec Λ _) :=
well_founded.intro (λ a, acc.intro a $ λ b ba,
  by { have : ∀ a : Λ, acc prec (some a),
       { intros a, apply precede.induction a,
         intros x IH, refine acc.intro _ (λ y yx, _),
         cases yx with _ z _ zx, apply IH _ zx },
       cases ba with b b a ba; exact this _ })

instance : precede (option Λ) := ⟨option.prec, option.prec.wf⟩

@[simp] lemma option.prec_none_simp {a : Λ} : (some a) ≺ none := option.prec.none

@[simp] lemma option.prec_some_simp {a b : Λ} : (some a) ≺ (some b) ↔ a ≺ b :=
⟨λ h, by { cases h with _ _ _ h, exact h }, option.prec.some⟩

inductive bool.prec : bool → bool → Prop
| intro : bool.prec tt ff

lemma bool.prec.trans : transitive bool.prec := λ _ _ _ ab bc, by cases ab; cases bc

lemma bool.prec.wf : well_founded bool.prec :=
well_founded.intro (λ a, acc.intro a $ λ b ba,
  by { cases ba, refine acc.intro _ (λ c ctt, _), cases ctt })

def prod.prec {α} : Λ × α → Λ × α → Prop := λ a b, a.1 ≺ b.1

lemma prod.prec.wf {α} : well_founded (@prod.prec Λ _ α) :=
well_founded.intro (λ a, acc.intro a $ λ b ba,
  by { suffices : ∀ (a : Λ) (p : α), acc prod.prec (a, p),
       { have := this b.1 b.2, simp at this, exact this },
       intros a, apply precede.induction a,
       intros x IH p, refine acc.intro _ (λ q eqn_q, _),
       simp[prod.prec] at eqn_q,
       have := IH _ eqn_q q.2, simp at this, exact this })

theorem prod.precede (Λ α) [precede Λ] : precede (Λ × α) := ⟨prod.prec, prod.prec.wf⟩

lemma prod.prec.trans {α} (trans : transitive (@precede.prec Λ _)) :
  transitive (@prod.prec Λ _ α) :=
λ x y z, @trans x.1 y.1 z.1

instance : precede bool := ⟨bool.prec, bool.prec.wf⟩

instance : precede ℕ := ⟨(<), nat.lt_wf⟩

def kb_order (p q : ℕ → Λ) : Prop := ∃ u : ℕ, (∀ ⦃n⦄, n < u → p n = q n) ∧ p u ≺ q u

infix ` <KB `:80 := kb_order

theorem truepath {p : ℕ → ℕ → Λ} [inhabited Λ] (h : ∀ s, p (s + 1) <KB p s) :
  ∃ f : ℕ → Λ, ∀ n, ∃ s, ∀ t, s < t → p t n = f n :=
begin
  suffices :
    ∀ n₀, ∃ s, ∀ n, n ≤ n₀ → ∃ v, ∀ t, s < t → p t n = v,
  { have : ∀ n, ∃ v s, ∀ t, s < t → p t n = v,
    { intros n, rcases this n with ⟨s, hyp_s⟩, rcases hyp_s n (by refl) with ⟨v, hyp_v⟩,
      refine ⟨v, s, hyp_v⟩ },
    let f := (λ n, classical.epsilon $ λ v : Λ, ∃ s, ∀ t, s < t → p t n = v),
    have := λ n, classical.epsilon_spec (this n), simp at this, exact ⟨f, this⟩ },
  intros n₀, induction n₀ with n₀ IH, simp,
  { have : ∃ m, ∀ n, ¬p n 0 ≺ p m 0, from precede.enum_minimal (λ s, p s 0), 
    rcases this with ⟨m, lmm_m⟩, 
    refine ⟨m, p m 0, _⟩, 
    suffices :
      ∀ t, p (m + t) 0 = p m 0,
    { intros t eqn_t, rw (show t = m + (t - m), by omega), exact this _ },
    intros t, induction t with t IH, refl,
    rcases h (m + t) with ⟨u, lmm_u1, lmm_u2⟩,
    cases u,
    { exfalso,
      have : p (m + t + 1) 0 ≺ p m 0, simp[←IH, lmm_u2],
      have : ¬p (m + t + 1) 0 ≺ p m 0 := lmm_m (m + t + 1), contradiction },
    { simp[←IH], refine lmm_u1 (nat.succ_pos _) } },
  { rcases IH with ⟨s₀, IH⟩,
    have : ∃ m, ∀ t, ¬p (max (s₀ + 1) t) (n₀ + 1) ≺ p (max (s₀ + 1) m) (n₀ + 1),
    from precede.enum_minimal (λ s, p (max (s₀ + 1) s) (n₀ + 1)),
    rcases this with ⟨m, lmm_m⟩,
    let s₁ := max (s₀ + 1) m,
    have eqn_s₁ : s₀ < s₁, { simp[s₁], },
    refine ⟨s₁, λ n eqn_n, _⟩,
    have C : n ≤ n₀ ∨ n = n₀ + 1, from nat.of_le_succ eqn_n, cases C,
    { rcases IH _ C with ⟨v, lmm_v⟩, refine ⟨v, λ t eqn_t, _⟩, simp at eqn_t,
      have : s₀ < t, omega, exact lmm_v _ this },
    { refine ⟨p s₁ (n₀ + 1), _⟩,
      suffices : 
        ∀ t, p (s₁ + t) (n₀ + 1) = p s₁ (n₀ + 1),
      { intros t eqn_t, simp[C], rw (show t = s₁ + (t - s₁), by omega), exact this _ },
      intros t, induction t with t IHt, refl,
      rcases h (s₁ + t) with ⟨u, lmm_u1, lmm_u2⟩,
      have : n₀ + 1 < u,
      { have C1 : u < n₀ + 1 ∨ u = n₀ + 1 ∨ n₀ + 1 < u, from trichotomous _ _,
        cases C1,
        { exfalso,
          have C' : u ≤ n₀, from nat.lt_succ_iff.mp C1,
          rcases IH _ C' with ⟨v, lmm_v⟩,
          have eqn_v1 : p (s₁ + t) u = v, from lmm_v _ (nat.lt_add_right _ _ _ eqn_s₁),
          have eqn_v2 : p (s₁ + t + 1) u = v,
          { rw (show s₁ + t + 1 = s₁ + (t + 1), by refl), from lmm_v _ (nat.lt_add_right _ _ _ eqn_s₁) },
          simp [eqn_v1, eqn_v2] at lmm_u2, exact precede.antirefl lmm_u2 }, cases C1,
        { exfalso,
          simp[C1] at lmm_u2,
          have := lmm_m (s₁ + t + 1),
          simp[show s₀ + 1 ≤ s₁ + t + 1, by omega] at this,
          simp[IHt] at lmm_u2,
          exact this lmm_u2 },
        exact C1 },
      rw ←IHt,
      exact lmm_u1 this } }
end

theorem kb_order.trans (trans : transitive (@precede.prec Λ _)) {p₀ p₁ p₂ : ℕ → Λ} :
  p₀ <KB p₁ → p₁ <KB p₂ → p₀ <KB p₂ :=
begin
  rintros ⟨u₀, hyp_u₀, hyp_u₀1⟩,
  rintros ⟨u₁, hyp_u₁, hyp_u₁1⟩,
  refine ⟨min u₀ u₁, λ n eqn_n, _, _⟩,
  simp at eqn_n, simp [hyp_u₀ eqn_n.1, hyp_u₁ eqn_n.2],
  have : u₀ < u₁ ∨ u₀ = u₁ ∨ u₁ < u₀, from trichotomous _ _, cases this,
  { simp [le_of_lt this, ←(hyp_u₁ this), hyp_u₀1] }, cases this,
  { simp [this] at hyp_u₀1 ⊢, exact trans hyp_u₀1 hyp_u₁1 },
  { simp [le_of_lt this, (hyp_u₀ this), hyp_u₁1] }
end

def list.kb (l₀ l₁ : list Λ) := l₀.rnth <KB l₁.rnth

infix ` <KB* `:80 := list.kb

def list.kbeq (l₀ l₁ : list Λ) := l₀ = l₁ ∨ l₀ <KB* l₁

infix ` ≤KB* `:80 := list.kbeq

theorem list.kb.trans (trans : transitive (@precede.prec Λ _)) {l₀ l₁ l₂ : list Λ} :
  l₀ <KB* l₁ → l₁ <KB* l₂ → l₀ <KB* l₂ := kb_order.trans (option.prec.trans trans)

theorem list.kb.append (a : Λ ) (l : list Λ) : (a :: l) <KB* l :=
⟨l.length, λ _ eqn, list.rnth_cons _ eqn, by { simp, unfold_coes, simp }⟩

end kb

variables {Λ : Type*} [kb.precede Λ] {α : Type*} 

def models {Λ} (p : list Λ → Λ → Prop) : list Λ → Prop
| []       := true
| (a :: l) := p l a ∧ models l

def list.initial {α} (l : list α) (n : ℕ) : list α := l.drop (l.length - n)

@[simp] lemma list.initial_length_le {α} {l : list α} {n} : l.length ≤ n → l.initial n = l := λ h,
by { have : l.length - n = 0, omega, simp[list.initial, this] }

@[simp] lemma list.initial_length {α} {l : list α} {n : ℕ} (h : n < l.length) : (l.initial n).length = n :=
by simp [list.initial, h]; omega

@[simp] lemma list.initial_initial {α} (l : list α) (n m : ℕ) (h : n < m) : (l.initial m).initial n = l.initial n :=
by { simp[list.initial], congr, omega nat }

lemma list.initial_nth  {α} {l : list α} {n m : ℕ} {a} :
  (l.initial m).rnth n = some a → l.rnth n = some a :=
begin
  have eqn : l.length ≤ m ∨ m < l.length, from le_or_lt _ _, cases eqn, simp[eqn],
  revert eqn a m n,
  simp [list.initial],
  induction l with d l IH; simp,
  intros n m a eqn_m eqn_a, simp[show l.length + 1 - m = l.length - m + 1, by omega] at eqn_a,
  have C := eq_or_lt_of_le (nat.lt_succ_iff.mp eqn_m),
  cases C,
  { simp[←C] at eqn_a, simp[list.rnth_length_lt eqn_a], exact eqn_a },
  { have : n < l.length, { have := list.rnth_length_lt eqn_a, simp at this, omega},
    simp[this], apply IH C eqn_a }
end

theorem models_iff {α} {p : list α → α → Prop} {l} :
  models p l ↔ ∀ n a, l.rnth n = some a → p (l.initial n) a :=
begin
  split,
  { induction l with d l IH; simp[models, list.initial], { simp[list.rnth] },
    intros hyp1 hyp2 n a eqn_a,
    have eqn_n : n < l.length + 1, { have := list.rnth_length_lt eqn_a, simp at this, exact this },
    simp[(show l.length + 1 - n = (l.length - n) + 1, by omega)],
    have eqn_n' : n = l.length ∨ n < l.length, from eq_or_lt_of_le (nat.lt_succ_iff.mp eqn_n),
    cases eqn_n',
    { simp[eqn_n'], have : a = d, { simp[eqn_n'] at eqn_a, unfold_coes at eqn_a, simp at eqn_a, simp[eqn_a]},
      simp[this, hyp1] },
    { simp[eqn_n'] at eqn_a, refine IH hyp2 _ _ eqn_a } },
  { induction l with d l IH; simp[models, list.initial],
    intros h, have := h l.length d, simp at this, refine ⟨this rfl, IH (λ n a eqn_a, _)⟩,
    simp[list.initial], have := h n a,
    have eqn_n : n < l.length, { have := list.rnth_length_lt eqn_a, exact this },
    simp[(show l.length + 1 - n = (l.length - n) + 1, by omega)] at this, apply this,
    simp[list.rnth_cons d eqn_n], exact eqn_a }
end

structure Strategy :=
(interpret  : ℕ → α → list Λ → Λ → Prop)
(head       : α)
(attention  : ℕ → ℕ → α → list Λ → bool)
(renovate   : ℕ → ℕ → α → list Λ → α)
(initialize : ℕ → α → list Λ → Λ)
(revise     : ℕ → ℕ → α → list Λ → list Λ)

namespace Strategy
variables (S : @Strategy Λ _ α)

def initialize_proper := ∀ {s A δ},
models (S.interpret s A) δ → models (S.interpret (s + 1) A) (S.initialize s A δ :: δ)

def renovate_revise_proper := ∀ {s A δ m},
models (S.interpret s A) δ → 
nat.rfind_fin (λ m, S.attention s m A δ) s = some m →
models (S.interpret (s + 1) (S.renovate s m A δ)) (S.revise s m A δ)

theorem rhhhth : S.renovate_revise_proper := λ s A δ m hyp1 hyp2,
begin
  simp[models_iff] at hyp1 hyp2 ⊢,
end

def procedure : ℕ → α × list Λ
| 0     := (S.head, [])
| (s+1) := let a := (procedure s).1,
               δ := (procedure s).2,
               m := nat.rfind_fin (λ m, S.attention s m a δ) s in
  match m with
  | none   := (a, S.initialize s a δ :: δ)
  | some m := (S.renovate s m a δ, S.revise s m a δ)
  end

def result (s : ℕ) : α := (S.procedure s).1

def approxpath (s : ℕ) : list Λ := (S.procedure s).2

def full : Prop := ∀ n, ∃ s, ∀ {t}, s < t → n < (S.approxpath t).length

theorem revise_order_path (hr : ∀ s m a δ, S.revise s m a δ <KB* δ) :
  ∀ s, S.approxpath (s + 1) <KB* S.approxpath s :=
begin
  intros s, 
  simp[Strategy.approxpath, Strategy.procedure],
  cases C : nat.rfind_fin (λ m, S.attention s m (S.procedure s).1 (S.procedure s).2) s;
  simp[C, Strategy.procedure],
  exact kb.list.kb.append _ _,
  exact hr _ _ _ _
end

theorem truepath_exists (F : S.full) (H : ∀ s, S.approxpath (s + 1) <KB* S.approxpath s) :
  ∃ f : ℕ → Λ, ∀ n, ∃ s, ∀ t, s < t → (S.approxpath t).rnth n = f n :=
begin
  have : ∃ f : ℕ → option Λ, ∀ n, ∃ s, ∀ t, s < t → (S.approxpath t).rnth n = f n,
  from @kb.truepath _ _ (λ s, (S.approxpath s).rnth) _ H,
  rcases this with ⟨f, lmm⟩,
  have : ∀ n, (f n).is_some,
  { intros n, rcases lmm n with ⟨s₀, hyp_s₀⟩,
    rcases F n with ⟨s₁, hyp_s₁⟩,
    have eqn_n : (S.approxpath (max s₀ s₁ + 1) ).rnth n =
      some ((S.approxpath (max s₀ s₁ + 1)).reverse.nth_le n 
        (by simp; exact hyp_s₁ (nat.lt_succ_iff.mpr (by simp; right; refl)))),
    from list.nth_le_nth _,
    have := hyp_s₀ (max s₀ s₁ + 1) (nat.lt_succ_iff.mpr (by simp; left; refl)),
    simp [←this, eqn_n] },
  let f' := (λ n, option.get $ this n),
  have : ∀ n, f n = some (f' n), intros n, simp[f', this],  
  refine ⟨f', λ n, _⟩, unfold_coes, rw ←this, exact lmm _
end

theorem result_models_approxpath (hi : S.initialize_proper) (hr : S.renovate_revise_proper) (s) :
  models (S.interpret s (S.result s)) (S.approxpath s) :=
begin
  induction s with s IH; simp[Strategy.approxpath, Strategy.result, Strategy.procedure],
  cases C : nat.rfind_fin (λ m, S.attention s m (S.procedure s).fst (S.procedure s).snd) s with v;
  simp[C, Strategy.procedure],
  exact hi IH, exact hr IH C,
end



end Strategy

section FM

/- Λ := bool × ℕ × option ℕ -/

def interpret (s : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ))
  (a : bool × ℕ × option ℕ) : Prop :=
let e := δ.length.div2,
    A₀ := A.1,
    A₁ := A.2,
    b := a.1,
    x := a.2.1 in
cond b
  (∃ r, a.2.2 = some r ∧ 
    (∀ s r', s < δ.length → (δ.reverse.inth s).2.2 = some r' → r' < x) ∧
    cond δ.length.bodd
    (⟦e⟧ᵪ^A₁.fdecode [r] x = ff ∧ A₀.fdecode x = tt)
    (⟦e⟧ᵪ^A₀.fdecode [r] x = ff ∧ A₁.fdecode x = tt))
  true


def attention (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) : bool :=
let A₀ := A.1,
    A₁ := A.2,
    x  := (δ.reverse.inth m).2.1,
    r  := (δ.reverse.inth m).2.2 in
(r = none) && cond m.bodd (⟦m.div2⟧^A₁.fdecode [s] x = some ff) (⟦m.div2⟧^A₀.fdecode [s] x = some ff)

def renovate (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  list (ℕ × bool) × list (ℕ × bool) :=
let A₀ := A.1,
    A₁ := A.2,
    x  := (δ.reverse.inth m).2.1,
    r  := (δ.reverse.inth m).2.2 in
cond m.bodd ((x, tt) :: A₀, A₁) (A₀, (x, tt) :: A₁) 

def init (s : ℕ) (δ : list (bool × ℕ × option ℕ)) : bool × ℕ × option ℕ :=
(ff, (s), none)

@[simp]
def inititr (s : ℕ) (δ : list (bool × ℕ × option ℕ)) : ℕ → list (bool × ℕ × option ℕ)
| 0     := δ
| (n+1) := init s (inititr n) :: inititr n

theorem inititr_length (s δ) : ∀ n, (inititr s δ n).length = δ.length + n
| 0       := rfl
| (n + 1) := by simp[inititr, inititr_length n]; refl

def initialize (s : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  bool × ℕ × option ℕ := init s δ

def revise (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  list (bool × ℕ × option ℕ) :=
let x  := (δ.reverse.inth m).2.1,
    r  := (δ.reverse.inth m).2.2 in
inititr s ((tt, x, s) :: δ.initial m) (s - m)

lemma interpret_proper {s A l d} : interpret s A l d → interpret (s + 1) A l d :=
by simp[interpret]

lemma initialize_proper {s A δ} (h : models (interpret s A) δ) :
  models (interpret (s + 1) A) (initialize s A δ :: δ) :=
begin
  simp[models, interpret],
  cases C : (initialize s A δ).1; simp[C, interpret],
  { have : ∀ l, models (interpret s A) l → models (interpret (s + 1) A) l,
    { intros l, induction l with d l IH; simp[models],
      refine λ hyp1 hyp2, ⟨interpret_proper hyp1, IH hyp2⟩ },
    refine this _ h },
  { simp[initialize, init] at C, contradiction }
end

def renovate_revise_proper {s A δ m}
  (IH : models (interpret s A) δ)
  (ha : nat.rfind_fin (λ m, attention s m A δ) δ.length = some m) :
  models (interpret (s + 1) (renovate s m A δ)) (revise s m A δ) :=
begin
  simp[attention] at ha, rcases ha with ⟨ha1, ha2, ha3⟩,
  simp[models, revise], 
  suffices : ∀ t,
    models (interpret (s + 1) (renovate s m A δ))
    (inititr s ((tt, (δ.reverse.nth m).iget.snd.fst, s) :: δ.initial m) t),
  { exact this _ },
  intros t, induction t; simp[models, inititr, renovate],
  { split,
    { cases C : m.bodd; simp[C, interpret, le_of_lt ha1] at ha2 ⊢; simp[C, ha1],
      { refine ⟨s, rfl, ha2.2, rfl⟩, },
      { refine ⟨s, rfl, ha2.2, rfl⟩, } },
    { cases C : m.bodd; simp[C, interpret, le_of_lt ha1] at ha2 ⊢,
      { simp[models_iff, interpret] at IH ⊢,
        intros n a eqn_a, have := list.rnth_length_lt eqn_a, simp[this],
        have eqn_n : n < δ.length, { simp[list.initial] at this, omega },
        have := IH n a (list.initial_nth eqn_a), 
          }
       } }

end

def renovate_revise_proper {s A δ m}
  (IH : models (interpret s A) δ)
  (ha : nat.rfind_fin (λ m, attention s m A δ) δ.length = some m) :
  models (interpret (s + 1) (renovate s m A δ)) (revise s m A δ) :=
begin
  simp[attention] at ha, rcases ha with ⟨ha1, ha2, ha3⟩,
  simp[models_iff] at IH ⊢,

end


/-
def prec (x y : (bool × ℕ × option ℕ)) : Prop := x.1 ≺ y.1

local attribute [instance]
theorem Λ_prec : kb.precede (bool × ℕ × option ℕ) := kb.prod.precede _ _

def S : Strategy := ⟨interpret, ([], []), attention, renovate, initialize, revise⟩

theorem approxpath_length (s) : (S.approxpath s).length = s :=
begin
  simp[Strategy.approxpath],
  induction s with s IH; 
  simp[Strategy.procedure], 
  cases C : nat.rfind_fin (λ m, S.attention s m (S.procedure s).1 (S.procedure s).2) s with m,
  simp[Strategy.procedure, IH],
  simp at C, have := C.1,
  have : S.revise = revise := rfl,
  simp[Strategy.procedure, revise, this, IH, inititr_length, le_of_lt C.1, list.initial],
  omega
end

theorem full : S.full := λ n, ⟨n, by simp[approxpath_length]⟩

theorem witness {s} : ∀ n x r, (strategy s).nth (bit0 n) = some ⟨tt, x, r⟩ →
  (A₀ s).fdecode x = tt ∧ ⟦x⟧ᵪ^(A₀ s).fdecode [s] (x) = ff :=
begin
  simp[strategy, approx],
  induction s with s IH; simp[strategy.approx],
end
-/
/--
((
  [ (94, tt), (89, tt), (87, tt), (85, tt), (81, tt), (79, tt), (75, tt), (75, tt),
    (73, tt), (71, tt), (45, tt), #(55, tt), (51, tt), (49, tt), (47, tt), (45, tt),
    (43, tt), (42, tt), (23, tt), (38, tt), (34, tt), (30, tt), (26, tt), (21, tt),
    (18, tt), (12, tt), (10, tt), (2, tt),  (0, tt) ],
  [ (95, tt), (90, tt), (87, tt), (83, tt), (80, tt), (76, tt), (74, tt), (72, tt),
    #(57, tt), (53, tt), (50, tt), (48, tt), (46, tt), (44, tt), (41, tt), (39, tt),
    (35, tt), (31, tt), (27, tt), (23, tt), (22, tt), (20, tt), (13, tt), (15, tt),
    (11, tt), (3, tt),  (1, tt) ] ),

  [ (tt, (0, (some 1))),   (tt, (1, (some 2))),   (tt, (2, (some 3))),   (tt, (3, (some 4))),
    (ff, (4, none)),       (ff, (5, none)),       (ff, (6, none)),       (ff, (7, none)),
    (ff, (8, none)),       (ff, (9, none)),       (tt, (10, (some 11))), (tt, (11, (some 12))),
    (tt, (12, (some 13))), (tt, (13, (some 20))), (ff, (20, none)),      (tt, (20, (some 21))),
    (ff, (21, none)),      (ff, (21, none)),      (tt, (21, (some 22))), (tt, (22, (some 23))),
    (tt, (23, (some 41))), (ff, (41, none)),      (ff, (41, none)),      (tt, (41, (some 42))),
    (tt, (42, (some 43))), (ff, (43, none)),      (tt, (43, (some 44))), (tt, (44, (some 45))),
    (tt, (45, (some 71))), (ff, (71, none)),      (tt, (71, (some 72))), (tt, (72, (some 73))),
    (ff, (73, none)),      (ff, (73, none)),      (tt, (73, (some 74))), (tt, (74, (some 75))),
    (tt, (75, (some 79))), (ff, (79, none)),      (tt, (79, (some 80))), (tt, (80, (some 81))),
    (ff, (81, none)),      (ff, (81, none)),      (ff, (81, none)),      (ff, (81, none)),
    (ff, (81, none)),      (ff, (81, none)),      (tt, (81, (some 83))), (tt, (83, (some 85))),
    (ff, (85, none)),      (ff, (85, none)),      (ff, (85, none)),      (ff, (85, none)),
    (ff, (85, none)),      (ff, (85, none)),      (tt, (85, (some 87))), (tt, (87, (some 89))),
    (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),
    (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),
    (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),
    (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),
    (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)),      (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (ff, (89, none)), (tt, (89, (some 90))), (tt, (90, (some 91))), (ff, (91, none)), (ff, (91, none)), (ff, (91, none)), (ff, (91, none)), (ff, (92, none)), (ff, (93, none)), (tt, (94, (some 95))), (tt, (95, (some 96))), (ff, (96, none)), (ff, (97, none)), (ff, (98, none)), (ff, (99, none))])
-/

end FM

