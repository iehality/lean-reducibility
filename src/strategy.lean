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

class cord (α : Type*) :=
(ord : α → α → Prop)

infix ` ≺ `:80 := cord.ord
universes u
variables {Λ : Type u}
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

/- wf_truepath p = lim_{n → ∞} p n -/
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
  {p : ℕ → ℕ → Λ} (h : ∀ s, p (s + 1) <KB (p s)) {n t} :
  wf_truepath_step p n ≤ t → p t n = wf_truepath p n :=
λ eqn_t, wf_truepath_step_spec wf h n n t (by refl) eqn_t

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
    sorry },
  sorry
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

@[refl, simp] theorem list.kbeq.refl (x : list Λ) : x ≤KB* x := by simp[list.kbeq]

theorem list.kb.trans (trans : transitive ((≺) : Λ → Λ → Prop)) {l₀ l₁ l₂ : list Λ} :
  l₀ <KB* l₁ → l₁ <KB* l₂ → l₀ <KB* l₂ := kb_order.trans (option.ord.trans trans)

@[simp]theorem list.kb.cons (a : Λ) (u : list Λ) : (a :: u) <KB* u :=
⟨u.length, λ _ eqn, list.rnth_cons eqn, by simp⟩

theorem list.kb.length_append {u₀ u₁ : list Λ}
  (h : u₀ <KB* u₁) (eqn : u₀.length = u₁.length) (v₀ v₁ : list Λ) :
  v₀ ++ u₀ <KB* v₁ ++ u₁ :=
begin
  rcases h with ⟨m, hyp1, hyp2⟩,
  cases option.ord_cases hyp2 with C C,
  { exfalso, rcases C with ⟨a, C1, C2⟩,
    simp[←eqn] at C2, 
    exact nat.lt_le_antisymm (list.rnth_some_lt C1) C2 },
  rcases C with ⟨a, b, C1, C2, C3⟩,
  refine ⟨m, _, _⟩,
  { intros n eqn_n,
    have eqn1 : n < u₀.length := lt_trans eqn_n (list.rnth_some_lt C1),
    have eqn2 : n < u₁.length := lt_trans eqn_n (list.rnth_some_lt C2),
    simp[list.rnth_append eqn1, list.rnth_append eqn2],
    exact hyp1 eqn_n },
  { have eqn1 : m < u₀.length := list.rnth_some_lt C1,
    have eqn2 : m < u₁.length := list.rnth_some_lt C2,
    simp[list.rnth_append eqn1, list.rnth_append eqn2],
    exact hyp2 }
end

theorem list.kb.length_cons {u₀ u₁ : list Λ}
  (h : u₀ <KB* u₁) (eqn : u₀.length = u₁.length) (a₀ a₁ : Λ) :
  a₀ :: u₀ <KB* a₁ :: u₁ :=
list.kb.length_append h eqn [a₀] [a₁]

theorem list.kb.length_cons_left {u₀ u₁ : list Λ}
  (h : u₀ ≤KB* u₁) (eqn : u₀.length = u₁.length) (a : Λ) : a :: u₀ <KB* u₁ :=
by { cases h, have := list.kb.length_append h eqn [a] [], simp at this, exact this,
     simp[h] }

theorem list.kb.cons_cons {u : list Λ} {a b : Λ} (h : a ≺ b) : a :: u <KB* b :: u :=
⟨u.length, λ n eqn_n, by simp[list.rnth_cons eqn_n], by simp[h]⟩

theorem list.kbeq.cons_cons {u : list Λ} {a b : Λ} (h : a ≼ b) : a :: u ≤KB* b :: u :=
by { cases h with h _ _ h, refl, left, exact list.kb.cons_cons h }

namespace wford
variables {p : ℕ → list Λ}  

noncomputable def wf_truepath_aux (p : ℕ → list Λ) : ℕ → option Λ :=
wf_truepath (λ s, (p s).rnth)

noncomputable def wf_truepath_step (p : ℕ → list Λ) : ℕ → ℕ :=
wf_truepath_step (λ s, (p s).rnth)

private lemma wf_truepath_some
  (wf : well_founded ((≺) : Λ → Λ → Prop)) (H : ∀ s, p (s + 1) <KB* p s) :
  ∀ n, (wf_truepath_aux p n).is_some := λ n,
begin
  suffices : wf_truepath_aux p n ≠ none,
  { cases wf_truepath_aux p n; simp at this ⊢, exact this },
  have := @wf_truepath_spec_neq _ _ (option.ord.wf wf) (λ s, (p s).rnth) H,
  apply this, simp[list.rnth],
  intros s n hyp, exact le_add_right hyp
end

noncomputable def wf_truepath (wf : well_founded ((≺) : Λ → Λ → Prop)) (H : ∀ s, p (s + 1) <KB* p s) : ℕ → Λ :=
λ n, option.get $ wf_truepath_some wf H n

theorem wf_truepath_spec (wf : well_founded ((≺) : Λ → Λ → Prop)) (H : ∀ s, p (s + 1) <KB* p s) {n t} :
  wf_truepath_step p n ≤ t → (p t).rnth n = some (wf_truepath wf H n) := λ eqn_t,
begin
  have := @wf_truepath_spec _ _ (option.ord.wf wf) (λ s, (p s).rnth) H _ _ eqn_t,
  simp at this, simp[this, wford.wf_truepath, wford.wf_truepath_aux], 
end

end wford

structure prio (Λ : Type*) [cord Λ] (α : Type*) :=
(head          : α)
(outcome       : ℕ → α → list Λ → Λ)
(action        : ℕ → α → list Λ → α)
(action_proper : ∀ {s A u}, outcome (s+1) A u = outcome s A u → action (s+1) A u = action s A u)

namespace prio
variables {α : Type u} (S : prio Λ α)

mutual def result_itr, approxpath_itr (s) 
with result_itr : ℕ → α
| 0     := S.head
| (n+1) := S.action s (result_itr n) (approxpath_itr n)
with approxpath_itr : ℕ → list Λ
| 0     := []
| (n+1) := (S.outcome s (result_itr n) (approxpath_itr n)) :: (approxpath_itr n)

def result (s) : α := S.result_itr s s

def approxpath (s) : list Λ := S.approxpath_itr s s

def procedure (s : ℕ) : ℕ → α × list Λ
| 0     := (S.head, [])
| (n+1) := let A₀ := (procedure n).1,
               u₀ := (procedure n).2 in
  (S.action s A₀ u₀, S.outcome s A₀ u₀ :: u₀)

lemma procedure_eq (s n) :
  S.procedure s n = (S.result_itr s n, S.approxpath_itr s n) :=
by induction n with n IH;
   simp[prio.procedure, prio.result_itr, prio.approxpath_itr] at*;
   simp[IH]

@[simp] lemma approxpath_length (s n) : (S.approxpath_itr s n).length = n :=
by induction n with n IH; simp[prio.approxpath_itr]; simp[IH]

theorem result_proper {s n} :
  S.approxpath_itr (s+1) n = S.approxpath_itr s n → S.result_itr (s+1) n = S.result_itr s n :=  
begin
  induction n with n IH; simp[prio.result_itr, prio.approxpath_itr],
  intros hyp1 hyp2, simp[hyp2, IH hyp2] at hyp1 ⊢, exact S.action_proper hyp1
end

end prio

structure iipm (Λ : Type*) [cord Λ] (α : Type*) extends prio Λ α :=
(infty : Λ)
(infty_proper : ∀ u, infty ≼ u)
(outcome_proper : ∀ s A u, outcome (s+1) A u ≼ outcome s A u ∨ outcome s A u = infty)

structure fipm (Λ : Type*) [cord Λ] (α : Type*) extends prio Λ α :=
(infty : Λ)
(infty_proper : ∀ u, infty ≼ u)
(wf : well_founded ((≺) : Λ → Λ → Prop))
(outcome_proper : ∀ s A u, outcome (s+1) A u ≼ outcome s A u)

namespace fipm
variables {α : Type u} (S : fipm Λ α)

@[simp] theorem approxpath_itr_kble (s n) :
  S.to_prio.approxpath_itr (s+1) n ≤KB* S.to_prio.approxpath_itr s n :=
begin
  induction n with n IH; simp[prio.result_itr, prio.approxpath_itr] at*,
  cases IH,
  { left, refine list.kb.length_cons IH _ _ _, simp },
  { simp[IH], apply list.kbeq.cons_cons,
    simp[S.to_prio.result_proper IH], exact S.outcome_proper _ _ _ }
end

theorem approxpath_kblt (s) :
  S.to_prio.approxpath (s+1) <KB* S.to_prio.approxpath s :=
by simp[prio.approxpath, prio.approxpath_itr];
   apply list.kb.length_cons_left; simp

noncomputable def wf_truepath : ℕ → Λ :=
wford.wf_truepath S.wf S.approxpath_kblt

noncomputable def wf_truepath_step : ℕ → ℕ := 
wford.wf_truepath_step S.to_prio.approxpath

theorem truepath_spec {n t} :
  S.wf_truepath_step n ≤ t → (S.to_prio.approxpath t).rnth n = some (S.wf_truepath n) :=
wford.wf_truepath_spec _ _

theorem truepath_part {u : list Λ} (h : ∀ n a, u.rnth n = some a → S.wf_truepath n = a) :
  ∃ v, u ⊆ v ∧  

end fipm





