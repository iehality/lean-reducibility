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

def kborder {α} (r : α → α → Prop) (p q : ℕ → α) : Prop :=
∃ u : ℕ, (∀ ⦃n⦄, n < u → p n = q n) ∧ r (p u) (q u)

section
parameters {α : Sort*} {r : α → α → Prop}
local infix `≺`:50    := r

lemma well_founded.minimal (wf : well_founded (≺))  {C : α → Prop}(h : ∃ x, C x) :
  ∃ m, C m ∧ ∀ x, x ≺ m → ¬C x:=
begin
  suffices : ∀ a, C a → ∃ m, C m ∧ ∀ x, x ≺ m → ¬C x,
  { rcases h with ⟨a, ha⟩, refine this _ ha },
  intros a,
  apply wf.induction a,
  intros a IH Ca,
  by_cases C : ∃ b, b ≺ a ∧ C b,
  { rcases C with ⟨b, hyp_b, hyp_b1⟩, refine IH b hyp_b hyp_b1 },
  { simp at C, refine ⟨a, Ca, C⟩ }
end

lemma well_founded.enum_minimal (wf : well_founded (≺)) {β} [inhabited β] (f : β → α) :
 ∃ m, ∀ n, ¬f n ≺ f m :=
begin
  let C := (λ x, ∃ n, f n = x),
  have := @well_founded.minimal wf C ⟨f (default β), ⟨(default β), rfl⟩⟩,
  simp[C] at this, rcases this with ⟨w, hyp_w⟩,
  refine ⟨w, λ n A, _⟩, have := hyp_w (f n) A,
  have := this n, simp at this, exact this
end

lemma well_founded.antirefl (wf : well_founded (≺)) {a : α} : ¬a ≺ a :=
by { have := well_founded.enum_minimal wf (λ n : ℕ, a), simp at this, exact this }

end

namespace kb

class cord (α : Type*) :=
(ord : α → α → Prop)

infix ` ≺ `:80 := cord.ord

variables {Λ : Type*}
variables [cord Λ]

inductive cordeq : Λ → Λ → Prop
| eq {x}     : cordeq x x
| cord {x y} : x ≺ y → cordeq x y

infix ` ≼ `:80 := cordeq

inductive option.ord : option Λ → option Λ → Prop
| none {a} : option.ord (some a) none
| some {a b} : a ≺ b → option.ord (some a) (some b)

lemma option.ord.trans (trans : transitive ((≺) : Λ → Λ → Prop)) :
  transitive (@option.ord Λ _) :=
λ a b c ab bc,
begin
  cases ab with a a b ab',
  { cases bc },
  { cases bc with _ _ c bc', exact option.ord.none,
    exact option.ord.some (trans ab' bc'), }
end

lemma option.ord.wf (h : well_founded ((≺) : Λ → Λ → Prop)) :
  well_founded (@option.ord Λ _) :=
well_founded.intro (λ a, acc.intro a $ λ b ba,
  by { have : ∀ a : Λ, acc option.ord (some a),
       { intros a, apply h.induction a,
         intros x IH, refine acc.intro _ (λ y yx, _),
         cases yx with _ z _ zx, apply IH _ zx },
       cases ba with b b a ba; exact this _ })

instance : cord (option Λ) := ⟨option.ord⟩

@[simp] lemma option.prec_none_simp {a : Λ} : (some a) ≺ none := option.ord.none

@[simp] lemma option.prec_some_simp {a b : Λ} : (some a) ≺ (some b) ↔ a ≺ b :=
⟨λ h, by { cases h with _ _ _ h, exact h }, option.ord.some⟩

lemma option.ord_cases {x y : option Λ} :
  x ≺ y → (∃ x', x = some x' ∧ y = none) ∨ (∃ x' y', x = some x' ∧ y = some y' ∧ x' ≺ y') := λ hyp,
by { cases hyp with x' x' y' hyp1; simp, exact hyp1 }

inductive bool.ord : bool → bool → Prop
| intro : bool.ord tt ff

lemma bool.ord.trans : transitive bool.ord := λ _ _ _ ab bc, by cases ab; cases bc

lemma bool.ord.wf : well_founded bool.ord :=
well_founded.intro (λ a, acc.intro a $ λ b ba,
  by { cases ba, refine acc.intro _ (λ c ctt, _), cases ctt })

instance : cord bool := ⟨bool.ord⟩

def prod.pord {α} : Λ × α → Λ × α → Prop := λ a b, a.1 ≺ b.1

lemma prod.pord.wf {α} (h : well_founded ((≺) : Λ → Λ → Prop)) : well_founded (@prod.pord Λ _ α) :=
well_founded.intro (λ a, acc.intro a $ λ b ba,
  by { suffices : ∀ (a : Λ) (p : α), acc prod.pord (a, p),
       { have := this b.1 b.2, simp at this, exact this },
       intros a, apply h.induction a,
       intros x IH p, refine acc.intro _ (λ q eqn_q, _),
       simp[prod.pord] at eqn_q,
       have := IH _ eqn_q q.2, simp at this, exact this })

lemma prod.pord.trans {α} (trans : transitive ((≺) : Λ → Λ → Prop)) :
  transitive (@prod.pord Λ _ α) :=
λ x y z, @trans x.1 y.1 z.1

def kb_order (p q : ℕ → Λ) : Prop := ∃ u : ℕ, (∀ ⦃n⦄, n < u → p n = q n) ∧ p u ≺ q u

infix ` <KB `:80 := kb_order

noncomputable def wf_truepath_step (p : ℕ → ℕ → Λ) : ℕ → ℕ :=
λ n₀, classical.epsilon (λ s, ∀ n t, n ≤ n₀ → s ≤ t → p t n = p s n)

noncomputable def wf_truepath (p : ℕ → ℕ → Λ) : ℕ → Λ :=
λ n, p (wf_truepath_step p n) n

theorem wf_truepath_step_spec (wf : well_founded ((≺) : Λ → Λ → Prop))
  {p : ℕ → ℕ → Λ} (h : ∀ s, p (s + 1) <KB (p s)) :
  ∀ n₀ n t, n ≤ n₀ → wf_truepath_step p n₀ ≤ t → p t n = p (wf_truepath_step p n₀) n :=
begin
  suffices :
    ∀ n₀, ∃ s, ∀ n t, n ≤ n₀ → s ≤ t → p t n = p s n,
  { have := λ n, classical.epsilon_spec (this n), simp at this, exact this },
  intros n₀, induction n₀ with n₀ IH, simp,
  { suffices : ∃ s, ∀ t, s ≤ t → p t 0 = p s 0,
    { rcases this with ⟨s, hyp⟩, refine ⟨s, λ n t eqn , _⟩, rw eqn, exact hyp _ },
    have : ∃ m, ∀ n, ¬p n 0 ≺ p m 0, from wf.enum_minimal (λ s, p s 0), 
    rcases this with ⟨m, lmm_m⟩, 
    refine ⟨m, _⟩, 
    suffices :
      ∀ t, p (m + t) 0 = p m 0,
    { intros t eqn_t, rw (show t = m + (t - m), by omega), exact this _ },
    intros t, induction t with t IH, refl,
    rcases h (m + t) with ⟨u, lmm_u1, lmm_u2⟩,
    cases u,
    { exfalso,
      have : p (m + t + 1) 0 ≺ p m 0, simp[←IH, lmm_u2],
      have : ¬p (m + t + 1) 0 ≺ p m 0, from lmm_m _, contradiction },
    { simp[←IH], refine lmm_u1 (nat.succ_pos _) } },
  { suffices :
      ∃ s, ∀ n t, n ≤ n₀.succ → p (s + t) n = p s n,
    { rcases this with ⟨s, hyp⟩, refine ⟨s, λ n t eqn_n eqn_t, _⟩, 
      have := hyp _ (t - s) eqn_n, simp[show s + (t - s) = t, by omega] at this,
      exact this },
    rcases IH with ⟨s₀, IH⟩,
    have : ∃ m, ∀ t, ¬p (max s₀ t) (n₀ + 1) ≺ p (max s₀ m) (n₀ + 1),
    from wf.enum_minimal (λ s, p (max s₀ s) (n₀ + 1)),
    rcases this with ⟨m, lmm_m⟩,
    let s₁ := max s₀ m,
    have eqn_s₁ : s₀ ≤ s₁, { simp[s₁], left, refl },
    refine ⟨s₁, λ n t eqn_n, _⟩,
    have C : n ≤ n₀ ∨ n = n₀ + 1, from nat.of_le_succ eqn_n, cases C,
    { have eqn1 : p (s₁ + t) n = p s₀ n, from IH _ _ C (le_add_right eqn_s₁),
      have eqn2 : p s₁ n = p s₀ n, from IH _ _ C eqn_s₁,
      simp[eqn1, eqn2] },
    induction t with t IHt, refl,
    { rcases h (s₁ + t) with ⟨u, lmm_u1, lmm_u2⟩,
      have : n₀ + 1 < u,
      { have C1 : u < n₀ + 1 ∨ u = n₀ + 1 ∨ n₀ + 1 < u, from trichotomous _ _,
        cases C1,
        { exfalso,
          have C' : u ≤ n₀, from nat.lt_succ_iff.mp C1,
          have eqn1 : p (s₁ + t) u = p s₀ u, from IH _ _ C' (le_add_right eqn_s₁),
          have eqn2 : p (s₁ + t + 1) u = p s₀ u, simp[add_assoc], from IH _ _ C' (le_add_right eqn_s₁),
          simp[eqn1, eqn2] at lmm_u2, exact wf.antirefl lmm_u2 }, cases C1,
        { exfalso,
          simp[C, C1] at lmm_u1 lmm_u2 IHt,
          have : ¬p (s₁ + t + 1) (n₀ + 1) ≺ p (s₁ + t) (n₀ + 1),
          { have := lmm_m (s₁ + t + 1), simp[show s₀ ≤ s₁ + t + 1, by omega] at this,
            simp[IHt], exact this },
          exact this lmm_u2 },
        exact C1 },
      simp[←nat.add_one, ←add_assoc],
      have : p (s₁ + t + 1) n = p (s₁ + t) n, simp[C], from lmm_u1 this,
      simp[this, IHt] } }
end

theorem wf_truepath_spec (wf : well_founded ((≺) : Λ → Λ → Prop))
  {p : ℕ → ℕ → Λ} (h : ∀ s, p (s + 1) <KB (p s)) :
  ∀ n t, wf_truepath_step p n ≤ t → p t n = wf_truepath p n :=
λ n t eqn_t, wf_truepath_step_spec wf h n n t (by refl) eqn_t

theorem wf_truepath_spec_neq (wf : well_founded ((≺) : Λ → Λ → Prop))
  {p : ℕ → ℕ → Λ} (h : ∀ s, p (s + 1) <KB (p s))
  {u : Λ} (hu : ∀ s n, p s n = u → p s (n + 1) = u) (n) : wf_truepath p n ≠ u := λ A,
begin
  have hu' : ∀ s n m, n < m → p s n = u → p s m = u,
  { suffices :
      ∀ s n m, p s n = u → p s (n + m) = u,
    { intros s n m eqn eqn_n, rw (show m = n + (m - n), by omega), refine this _ _ _ eqn_n },
    intros s n m hyp, induction m with m IH, exact hyp,
    simp[←nat.add_one, ←add_assoc], refine hu _ _ IH },
  let s₀ := wf_truepath_step p n,
  have A : p s₀ n = u, from A,
  rcases h s₀ with ⟨m, lmm_m1, lmm_m2⟩,
  have : p (s₀ + 1) m = p s₀ m,
  { have eqn : m ≤ n ∨ n < m, from le_or_lt _ _,
    cases eqn,
    { exact wf_truepath_step_spec wf h n m (s₀ + 1) eqn (by simp) },
    { have : p s₀ m = u, refine hu' _ _ _ eqn A, simp[this],
      have : p (s₀ + 1) n = u, simp[lmm_m1 eqn, A],
      have : p (s₀ + 1) m = u, refine hu' _ _ _ eqn this, simp[this] } },
  simp[this] at lmm_m2,
  exact wf.antirefl lmm_m2,
end

noncomputable def lim_truepath (p : ℕ → ℕ → Λ) : ℕ → Λ ⊕ unit :=
(λ n, classical.epsilon $ λ v,
  ((∃ s, ∀ t, s < t → p (t + 1) n = p t n) ∧ (∃ s, ∀ t, s < t → v = sum.inl (p t n))) ∨
  ((∀ s, ∃ t, s < t ∧ p (t + 1) n ≺ p t n) ∧ (v = sum.inr ())))

theorem lim_truepath_spec [inhabited Λ] {p : ℕ → ℕ → Λ}
  (h : ∀ s, p (s + 1) <KB (p s)) (n) :
  ((∃ s, ∀ t, s < t → p (t + 1) n = p t n) ∧ (∃ s, ∀ t, s < t → lim_truepath p n = sum.inl (p t n))) ∨
  ((∀ s, ∃ t, s < t ∧ p (t + 1) n ≺ p t n) ∧ (lim_truepath p n = sum.inr ())) :=
begin
  suffices : ∃ z,
    ((∃ s, ∀ t, s < t → p (t + 1) n = p t n) ∧ (∃ s, ∀ t, s < t → z = sum.inl (p t n))) ∨
    ((∀ s, ∃ t, s < t ∧ p (t + 1) n ≺ p t n) ∧ (z = sum.inr ())),
  from classical.epsilon_spec this,
  by_cases C : ∃ s, ∀ t, s < t → p (t + 1) n = p t n,
  { rcases C with ⟨s, C⟩, use sum.inl (p (s + 1) n), left,
    refine ⟨⟨s, C⟩, s, λ t eqn_t, _⟩, simp,
     }
  
end

theorem kb_order.trans (trans : transitive ((≺) : Λ → Λ → Prop)) {p₀ p₁ p₂ : ℕ → Λ} :
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

infix ` <KB* `:40 := list.kb

def list.kbeq (l₀ l₁ : list Λ) := l₀ <KB* l₁ ∨ l₀ = l₁ 

infix ` ≤KB* `:40 := list.kbeq

theorem list.kb.trans (trans : transitive ((≺) : Λ → Λ → Prop)) {l₀ l₁ l₂ : list Λ} :
  l₀ <KB* l₁ → l₁ <KB* l₂ → l₀ <KB* l₂ := kb_order.trans (option.ord.trans trans)

@[simp]theorem list.kb.append (a : Λ) (u : list Λ) : (a :: u) <KB* u :=
⟨u.length, λ _ eqn, list.rnth_cons eqn, by simp⟩

theorem list.kb.concat {u₀ u₁ : list Λ} (h : u₀ <KB* u₁) (v₀ v₁ : list Λ) :
  v₀ ++ u₀ <KB* v₁ ++ u₁ :=
begin
  rcases h with ⟨m, hyp1, hyp2⟩,
  cases option.ord_cases hyp2 with C C;
  refine ⟨m, _, _⟩,
  { intros n eqn_m,
    rcases C with ⟨a, C1, C2⟩,
      have eqn1 : n < u₀.length := lt_trans eqn_m (list.rnth_some_lt C1),
      have eqn2 : n < u₁.length, 
      { have : u₀.rnth n = some _ := list.rnth_le_rnth eqn1,
        simp[hyp1 eqn_m] at this, exact list.rnth_some_lt this },
      simp[list.rnth_append eqn1, list.rnth_append eqn2],
      exact hyp1 eqn_m },
  { rcases C with ⟨a, C1, C2⟩,
    have : (v₁ ++ u₁).rnth m = none,
    { simp,  } }
end

theorem list.kb.concat {u₀ u₁ : list Λ} (h : u₀ <KB* u₁) (v₀ v₁ : list Λ) :
  v₀ ++ u₀ <KB* v₁ ++ u₁ :=
begin
  rcases h with ⟨m, hyp1, hyp2⟩,
  refine ⟨m, _, _⟩,
  { intros n eqn_m,
    cases option.ord_cases hyp2 with C C,
    { rcases C with ⟨a, C1, C2⟩,
      have eqn1 : n < u₀.length := lt_trans eqn_m (list.rnth_some_lt C1),
      have eqn2 : n < u₁.length, 
      { have : u₀.rnth n = some _ := list.rnth_le_rnth eqn1,
        simp[hyp1 eqn_m] at this, exact list.rnth_some_lt this },
      simp[list.rnth_append eqn1, list.rnth_append eqn2],
      exact hyp1 eqn_m },
    { rcases C with ⟨a, b, C1, C2, eqn⟩,
      have eqn1 : n < u₀.length := lt_trans eqn_m (list.rnth_some_lt C1),
      have eqn2 : n < u₁.length := lt_trans eqn_m (list.rnth_some_lt C2),
      simp[list.rnth_append eqn1, list.rnth_append eqn2],
      exact hyp1 eqn_m } },
  {  }
end

@[simp] theorem list.kbeq.refl (x : list Λ) : x ≤KB* x := by simp[list.kbeq]
end kb

variables {Λ : Type*} [kb.cord Λ] {α : Type*} 

@[simp]
def models {Λ} (p : list Λ → Λ → Prop) : list Λ → Prop
| []       := true
| (a :: l) := p l a ∧ models l

theorem models_iff {α} {p : list α → α → Prop} {l} :
  models p l ↔ ∀ n a, l.rnth n = some a → p (l↾*n) a :=
begin
  induction l with d l IH; simp,
  split,
  { rintros ⟨hyp1, hyp2⟩, intros n a eqn_a,
    have : n = l.length ∨ n < l.length,
    { have := list.rnth_some_lt eqn_a, simp at this,
      exact eq_or_lt_of_le (nat.lt_succ_iff.mp this) },
    cases this, { simp[this] at eqn_a, simp[←eqn_a, this], exact hyp1 },
    { simp[list.initial_cons this, list.rnth_cons this] at eqn_a ⊢,
      refine IH.mp hyp2 _ _ eqn_a } },
  { intros h, split,
    { have := h l.length d, simp at this, exact this },
    { refine IH.mpr (λ n a eqn_a, _),
      have lmm := h n a,
      have := list.rnth_some_lt eqn_a,
      simp[list.rnth_cons this, list.initial_cons this] at lmm, 
      refine lmm eqn_a } }
end

notation `∞` := tt



structure prio (Λ : Type*) [kb.cord Λ] (α : Type*) :=
(head    : α)
(outcome : ℕ → α → list Λ → Λ)
(action  : ℕ → α → list Λ → α)

namespace prio
variables (S : prio Λ α)

def procedure (s : ℕ) : ℕ → α × list Λ
| 0     := (S.head, [])
| (n+1) := let A₀ := (procedure n).1,
               u₀ := (procedure n).2 in
  (S.action s A₀ u₀, u₀ ++ [S.outcome s A₀ u₀])

def result (s : ℕ) : α := (S.procedure s s).1

def approxpath (s : ℕ) := (S.procedure s s).2

lemma approxpath_length (s) : (S.approxpath s).length = s :=
begin
  suffices : ∀ n, (S.procedure s n).2.length = n,
  { exact this s },
  intros n, induction n with n IH; simp[procedure], simp[IH]
end

end prio

structure iipm (Λ : Type*) [kb.cord Λ] (α : Type*) extends prio Λ α :=
(infty : Λ)
(infty_proper : ∀ u, infty ≼ u)
(outcome_proper : ∀ s A u, outcome (s+1) A u ≼ outcome s A u ∨ outcome s A u = infty)

structure fipm (Λ : Type*) [kb.cord Λ] (α : Type*) extends prio Λ α :=
(infty : Λ)
(infty_proper : ∀ u, infty ≼ u)
(wf : well_founded ((≺) : Λ → Λ → Prop))
(outcome_proper : ∀ s A u, outcome (s+1) A u ≼ outcome s A u)

namespace fipm
variables (S : fipm Λ α)

#check S.head

def finiteinjury : Prop := ∀ s A u, S.outcome (s+1) A u ≼ S.outcome s A u 

theorem finiteinjury_kbprec (h : S.finiteinjury) :
  ∀ s, S.to_prio.approxpath (s+1) <KB* S.to_prio.approxpath s :=
begin
  have : ∀ s n, (S.to_prio.procedure (s+1) n).2 ≤KB* (S.to_prio.procedure s n).2,
  { intros s n, induction n with n IH; simp[prio.procedure],
    cases IH,
    {  } }

end
end fipm




structure Strategy :=
(interpret  : ℕ → α → list Λ → Λ → Prop)
(head       : α)
(attention  : ℕ → ℕ → α → list Λ → bool)
(action     : ℕ → ℕ → α → list Λ → α)
(initialize : ℕ → α → list Λ → Λ)
(revise     : ℕ → ℕ → α → list Λ → list Λ)

namespace Strategy
variables (S : @Strategy Λ _ α)

def initialize_proper := ∀ {s A δ},
models (S.interpret s A) δ → models (S.interpret (s + 1) A) (S.initialize s A δ :: δ)

def validate_revise_proper := ∀ {s A δ m},
models (S.interpret s A) δ → 
nat.rfind_fin (λ m, S.attention s m A δ) s = some m →
models (S.interpret (s + 1) (S.action s m A δ)) (S.revise s m A δ)

theorem rhhhth : S.validate_revise_proper := λ s A δ m hyp1 hyp2,
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
  | some m := (S.action s m a δ, S.revise s m a δ)
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

noncomputable def wf_trupath_aux : ℕ → option Λ := kb.wf_truepath (λ s, (S.approxpath s).rnth)

noncomputable def wf_truepath_step : ℕ → ℕ := kb.wf_truepath_step (λ s, (S.approxpath s).rnth)

private lemma wf_truepath_some
  (wf : well_founded ((≺) : Λ → Λ → Prop))
  (H : ∀ s, S.approxpath (s + 1) <KB* S.approxpath s) :
  ∀ n, (S.wf_trupath_aux n).is_some := λ n,
begin
  suffices : S.wf_trupath_aux n ≠ none,
  { cases S.wf_trupath_aux n; simp at this ⊢, exact this },
  have := @kb.wf_truepath_spec_neq _ _ (kb.option.ord.wf wf) (λ s, (S.approxpath s).rnth) H,
  apply this, simp[list.rnth],
  intros s n hyp, exact le_add_right hyp
end

noncomputable def wf_truepath
  (wf : well_founded ((≺) : Λ → Λ → Prop))
  (H : ∀ s, S.approxpath (s + 1) <KB* S.approxpath s) : ℕ → Λ :=
(λ n, option.get $ wf_truepath_some S wf H n)

theorem wf_truepath_exists (wf : well_founded ((≺) : Λ → Λ → Prop))
  (H : ∀ s, S.approxpath (s + 1) <KB* S.approxpath s) {n t} :
  S.wf_truepath_step n ≤ t → (S.approxpath t).rnth n = S.wf_truepath wf H n := λ hyp,
begin
  have eqn1 : (S.approxpath t).rnth n = S.wf_trupath_aux n,
  from @kb.wf_truepath_spec _ _ (kb.option.ord.wf wf) (λ s, (S.approxpath s).rnth) H n t hyp,
  have eqn2 : S.wf_truepath wf H n = (option.get $ wf_truepath_some S wf H n), refl,
  unfold_coes, simp[eqn1, eqn2],
end

theorem result_models_approxpath (hi : S.initialize_proper) (hr : S.validate_revise_proper) (s) :
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
    (∀ s r', s < δ.length → (δ.irnth s).2.2 = some r' → r' < x) ∧
    cond δ.length.bodd
    (⟦e⟧ᵪ^A₁.fdecode [r] x = ff ∧ A₀.fdecode x = tt)
    (⟦e⟧ᵪ^A₀.fdecode [r] x = ff ∧ A₁.fdecode x = tt))
  true

def attention (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) : bool :=
let A₀ := A.1,
    A₁ := A.2,
    x  := (δ.irnth m).2.1,
    r  := (δ.irnth m).2.2 in
(r = none) && cond m.bodd (⟦m.div2⟧^A₁.fdecode [s] x = some ff) (⟦m.div2⟧^A₀.fdecode [s] x = some ff)

def action (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  list (ℕ × bool) × list (ℕ × bool) :=
let A₀ := A.1,
    A₁ := A.2,
    x  := (δ.irnth m).2.1,
    r  := (δ.irnth m).2.2 in
cond m.bodd ((x, tt) :: A₀, A₁) (A₀, (x, tt) :: A₁) 

def init (s : ℕ) (δ : list (bool × ℕ × option ℕ)) : bool × ℕ × option ℕ :=
(ff, (s), none)

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
let x  := (δ.irnth m).2.1,
    r  := (δ.irnth m).2.2 in
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

def validate_revise_proper {s A δ m}
  (IH : models (interpret s A) δ)
  (ha : nat.rfind_fin (λ m, attention s m A δ) δ.length = some m) :
  models (interpret (s + 1) (action s m A δ)) (revise s m A δ) :=
begin
  simp[attention] at ha, rcases ha with ⟨ha1, ha2, ha3⟩,
  simp[models, revise], 
  suffices : ∀ t,
    models (interpret (s + 1) (action s m A δ))
    (inititr s ((tt, (δ.irnth m).2.1, s) :: δ.initial m) t),
  { exact this _ },
  intros t, induction t; simp[models, inititr, action],
  { simp[models_iff, interpret] at IH ⊢, split,
    { cases C : m.bodd; simp[C, interpret, le_of_lt ha1] at ha2 ⊢, simp[C, ha1],
      { have := IH m ((δ.initial m).irnth s), refine ⟨s, rfl, _, ha2.2, rfl⟩, sorry },
      { refine ⟨s, rfl, _, ha2.2, rfl⟩, sorry } },
    { cases C : m.bodd; simp[C, interpret, le_of_lt ha1] at ha2 ⊢,
      { 
intros n a eqn_a, have := list.rnth_some_lt eqn_a, simp[this],
        have eqn_n : n < δ.length, { simp[list.initial] at this, omega },
        have := IH n a (list.initial_nth eqn_a), 
          }
       } }

end

def validate_revise_proper {s A δ m}
  (IH : models (interpret s A) δ)
  (ha : nat.rfind_fin (λ m, attention s m A δ) δ.length = some m) :
  models (interpret (s + 1) (action s m A δ)) (revise s m A δ) :=
begin
  simp[attention] at ha, rcases ha with ⟨ha1, ha2, ha3⟩,
  simp[models_iff] at IH ⊢,

end


/-
def prec (x y : (bool × ℕ × option ℕ)) : Prop := x.1 ≺ y.1

local attribute [instance]
theorem Λ_prec : kb.cord (bool × ℕ × option ℕ) := kb.prod.cord _ _

def S : Strategy := ⟨interpret, ([], []), attention, action, initialize, revise⟩

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

