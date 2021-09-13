import reducibility function  data.list.basic

open encodable denumerable t_reducible

local attribute [simp] set.set_of_app_iff

@[derive decidable_eq]
inductive infinity : Type
| infinity : infinity

@[derive decidable_eq]
inductive zero : Type
| zero : zero

def Tree' : ℕ → Type
| 0       := zero
| (n + 1) := list (infinity ⊕ Tree' n)

instance : ∀ n, decidable_eq (Tree' n)
| 0       := zero.decidable_eq
| (n + 1) := @list.decidable_eq _ (@sum.decidable_eq infinity _ _ (Tree'.decidable_eq n))

def Tree (n : ℕ) := Tree' (n + 1)

instance {n} : has_subset (Tree n) := ⟨(⊂ᵢ)⟩

def branch {n} (η : Tree n) := { μ : Tree n // μ ⊂ᵢ η }

structure Tree_path (n : ℕ) :=
(path : ℕ → Tree n)
(ordered : ∀ m, path m <:+ path (m + 1))

@[simp] lemma list.cons_neq {α : Type*} (a : α) : ∀ (l : list α), l ≠ a :: l
| [] := by simp
| (a₁ :: l) := by { simp, intros h, simp[h], exact list.cons_neq l }

def branch.cons' {n} {η : Tree n} {a} (μ : branch η) : branch (a :: η) :=
⟨μ.val, μ.property.trans (η.is_initial_cons _)⟩

instance : has_zero (zero ⊕ infinity) := ⟨sum.inl zero.zero⟩

notation `∞` := sum.inl infinity.infinity

@[simp] def list.foldl' {α : Type*} (f : α → α → α) : list α → option α
| []        := none
| (a :: as) := if h : (list.foldl' as).is_some then f (option.get h) a else a

structure strategy (R : Type*) :=
(par₀ : Tree 0 → ℕ)
(par₁ : Tree 1 → ℕ)
(requirement : Tree 1 × ℕ → R)
(computation : Tree 0 × R → Tree 0 × R → Prop)
(inf : Tree 1 × ℕ → Tree 1 × ℕ → Tree 1 × ℕ)

namespace strategy
variables {R : Type*} (S : strategy R)

def out {n} : Π {η : Tree n}, branch η → infinity ⊕ Tree' n
| []       ⟨μ, μ_p⟩ := by exfalso; simp* at*
| (ν :: η) ⟨μ, μ_p⟩ := if h : μ ⊂ᵢ η then out ⟨μ, h⟩ else ν

lemma out_eq_iff {n} : ∀ {η : Tree n} {μ : branch η} {ν}, out μ = ν ↔ ν :: μ.val <:+ η
| []       ⟨μ, μ_p⟩ _ := by exfalso; simp* at*
| (ν :: η) ⟨μ, μ_p⟩ ν' :=
    by { simp, have : μ = η ∨ μ ⊂ᵢ η, from list.is_initial_cons_iff.mp μ_p, cases this,
         { rcases this with rfl, simp[out], exact eq_comm },
         { simp[out, this],
           have IH : out ⟨μ, this⟩ = ν' ↔ ν' :: μ <:+ η, from @out_eq_iff η ⟨μ, this⟩ ν', rw IH,
           split,
           { intros h, refine list.suffix_cons_iff.mpr (or.inr h) },
           { intros h, have C := list.suffix_cons_iff.mp h, cases C,
             { exfalso, simp at C, rcases C with ⟨_, rfl⟩, simp at this, exact this },
             { exact C } } } }

lemma suffix_out_cons {n} {η : Tree n} (μ : branch η) : out μ :: μ.val <:+ η :=
by { have := @out_eq_iff n η μ (out μ), simp* at* }

lemma out_cons'_eq {n} {η : Tree n} (ν) (μ : branch η)  :
  @out n (ν :: η) μ.cons' = out μ :=
by { simp[out, branch.cons'], intros h, exfalso, have := h μ.property, exact this }

namespace approx

def weight (μ : Tree 1) : Π {η : Tree 0} (υ : branch η → option (Tree 1)), ℕ
| []       _ := 0
| (_ :: η) υ := @weight η (λ ν, υ ν.cons') + (if υ ⟨η, by simp⟩ = ↑μ then 1 else 0)

lemma of_weight_pos {μ : Tree 1} : ∀ {η : Tree 0}
  (υ : branch η → option (Tree 1)) (pos : 0 < weight μ υ), ∃ η₀ : branch η, υ η₀ = μ
| []       υ pos := by { exfalso, simp[weight] at pos, exact pos }
| (ν :: η) υ pos := by { 
    by_cases C : υ ⟨η, by simp⟩ = ↑μ; simp[C, weight] at pos,
    { refine ⟨⟨η, by simp⟩, C⟩ },
    { rcases @of_weight_pos η (λ ν, υ ν.cons') pos with ⟨η₀, η₀_h⟩,
      refine ⟨η₀.cons', η₀_h⟩ } }

lemma weight_pos_of {μ : Tree 1} : ∀ {η : Tree 0}
  (υ : branch η → option (Tree 1)) (h : ∃ η₀ : branch η, υ η₀ = μ), 0 < weight μ υ
| [] _ h := by { exfalso, rcases h with ⟨⟨_, h⟩, _⟩, simp at h, exact h }
| (ν :: η) υ h := by
    { rcases h with ⟨η₀, h⟩,
      have : η₀.val = η ∨ η₀.val ⊂ᵢ η, from list.is_initial_cons_iff.mp η₀.property,
      cases this,
      { simp[weight, ←this, h] },
      { simp[weight], have := @weight_pos_of η (λ ν, υ ν.cons') ⟨⟨η₀.val, this⟩, by simp[branch.cons', h]⟩,
        exact nat.add_pos_left this _ } }

def is_exists_inv_infinity (μ : Tree 1) :
  Π {η : Tree 0} (υ : branch η → option (Tree 1)), option (branch η)
| []               _ := none
| (sum.inl _ :: η) υ :=
    if (@is_exists_inv_infinity η (λ ν, υ ν.cons')).is_some then
      (@is_exists_inv_infinity η (λ ν, υ ν.cons')).map branch.cons' else
    if υ ⟨η, by simp⟩ = ↑μ then some ⟨η, by simp⟩ else none
| (sum.inr _ :: η) υ := (@is_exists_inv_infinity η (λ ν, υ ν.cons')).map branch.cons'

lemma is_some_of_out_infinity {η : Tree 1} :
  ∀ {μ : Tree 0} (υ : branch μ → option (Tree 1)) (μ₀ : branch μ)
  (h1 : out μ₀ = ∞) (h2 : υ μ₀ = η), (is_exists_inv_infinity η υ).is_some 
| []       υ μ₀ _  _  := by { exfalso, have := μ₀.property, simp* at*  }
| (ν :: μ) υ μ₀ h1 h2 :=
    begin
      have C₁ : μ₀.val = μ ∨ μ₀.val ⊂ᵢ μ, from list.is_initial_cons_iff.mp μ₀.property, cases C₁,
      { cases ν; simp[is_exists_inv_infinity] at*,
        { cases ν,
          cases C₂ : (@is_exists_inv_infinity η μ (λ ν, υ ν.cons')).is_some; simp[C₂],
          { simp[←C₁, h2] },
          { rcases option.is_some_iff_exists.mp C₂ with ⟨_, C₂⟩, simp[C₂] } },
        { exfalso, have := out_eq_iff.mp h1, simp[←C₁] at this, exact this } },
      { have IH : (is_exists_inv_infinity η (λ ν, υ ν.cons')).is_some,
          from @is_some_of_out_infinity μ (λ ν, υ ν.cons') ⟨μ₀.val, C₁⟩
        (by {rw ←out_cons'_eq ν ⟨μ₀.val, C₁⟩, simp[branch.cons', h1] })
        (by simp[branch.cons', h2]),
        cases ν; simp[is_exists_inv_infinity] at*; 
        rcases option.is_some_iff_exists.mp IH with ⟨_, IH⟩; simp[IH] }
    end

lemma out_infinity_of_eq_some {η : Tree 1} :
  ∀ {μ : Tree 0} (υ : branch μ → option (Tree 1)) {μ₀ : branch μ}
  (h : is_exists_inv_infinity η υ = some μ₀), out μ₀ = ∞ ∧ υ μ₀ = η
| []               _ μ₀ _ := by { exfalso, have := μ₀.property, simp* at* }
| (∞ :: μ)        υ μ₀ h :=
    begin
      cases C₁ : (@is_exists_inv_infinity η μ (λ ν, υ ν.cons')).is_some;
      simp[is_exists_inv_infinity, C₁] at h,
      { by_cases C₂ : υ ⟨μ, by simp⟩ = ↑η,
        { simp[C₂] at h,
          rcases h with rfl, simp[out_eq_iff, C₂] },
        { exfalso, simp[C₂] at h, exact h } },
      { rcases h with ⟨μ₁, h, eqn⟩,
        have IH : out μ₁ = ∞ ∧ υ μ₁.cons' = ↑η,
          from @out_infinity_of_eq_some _ (λ ν, υ ν.cons') μ₁ h,
        simp[←eqn, out_cons'_eq], exact IH }
    end
| (sum.inr ν :: μ) υ μ₀ h :=
    begin
      simp[is_exists_inv_infinity] at h,
      rcases h with ⟨μ₁, h, eqn⟩,
        have IH : out μ₁ = ∞ ∧ υ μ₁.cons' = ↑η,
          from @out_infinity_of_eq_some _ (λ ν, υ ν.cons') μ₁ h,
      simp[←eqn, out_cons'_eq], exact IH
    end

lemma out_neq_infinity_of_eq_none {η : Tree 1}
  {μ : Tree 0} (υ : branch μ → option (Tree 1))
  (h : is_exists_inv_infinity η υ = none) (μ₀ : branch μ) : υ μ₀ = η → out μ₀ ≠ ∞ :=
begin
  by_cases C : υ μ₀ = ↑η ∧ out μ₀ = ∞,
  { exfalso, have := is_some_of_out_infinity υ μ₀ C.2 C.1, simp[h] at this, exact this },
  { simp at C, exact C }
end

lemma eq_none_of_out_neq_infinity {η : Tree 1} :
  ∀ {μ : Tree 0} (υ : branch μ → option (Tree 1))
  (h : ∀ μ₀ : branch μ, υ μ₀ = η → out μ₀ ≠ ∞), is_exists_inv_infinity η υ = none
| []       _ _ := by simp[is_exists_inv_infinity]
| (ν :: μ) υ h :=
    begin
      have : ∀ (μ₀ : branch μ), υ μ₀.cons' = ↑η → out μ₀ ≠ ∞,
        { intros μ₀, simp[←out_cons'_eq ν μ₀, branch.cons'],
          have := h ⟨μ₀.val, μ₀.property.trans (μ.is_initial_cons _)⟩, exact this }, 
        have : is_exists_inv_infinity η (λ ν, υ ν.cons') = none,
          from eq_none_of_out_neq_infinity (λ ν, υ ν.cons') this,
        cases ν; simp[is_exists_inv_infinity, this],
        { cases ν, intros hμ,
          have : out ⟨μ, _⟩ ≠ ∞ := h ⟨μ, by simp⟩ hμ,
          simp[out_eq_iff] at this, exact this }
    end

def lambda' {η : Tree 0} (υ : branch η → option (Tree 1)) : ℕ → Tree 1
| 0       := []
| (n + 1) :=
    if 0 < weight (lambda' n) υ then
      if h : (is_exists_inv_infinity (lambda' n) υ).is_some then
        sum.inr (option.get h).val :: lambda' n
      else ∞ :: lambda' n
    else lambda' n

lemma lambda'_suffix_eq {η : Tree 0} (υ : branch η → option (Tree 1)) : ∀ {n : ℕ}
  {x} {μ : Tree 1} (hμ : x :: μ <:+ lambda' υ n),
  ∃ m, m < n ∧ lambda' υ m = μ ∧ lambda' υ (m + 1) = x :: μ
| 0       x μ h := by { exfalso, simp[lambda', *] at * }
| (n + 1) x μ h :=
    begin
      simp[lambda'] at h,
      by_cases C₁ : 0 < weight (lambda' υ n) υ; simp[C₁] at h,
      { cases C₂ : (is_exists_inv_infinity (lambda' υ n) υ).is_some; simp[C₂] at h,
        { have C₃ : x :: μ = ∞ :: lambda' υ n ∨ x :: μ <:+ lambda' υ n, from list.suffix_cons_iff.mp h,
          cases C₃,
          { simp at C₃, refine ⟨n, lt_add_one n, by simp[C₃], by simp[lambda', C₁, C₂, C₃]⟩ },
          { rcases @lambda'_suffix_eq n x μ C₃ with ⟨m, IH₁, IH₂⟩,
            refine ⟨m, nat.lt.step IH₁, IH₂⟩ } },
        { have C₃ : x :: μ = sum.inr (option.get C₂).val :: lambda' υ n ∨ x :: μ <:+ lambda' υ n,
            from list.suffix_cons_iff.mp h,
          cases C₃,
          { simp at C₃, refine ⟨n, lt_add_one n, by simp[C₃], by simp[lambda', C₁, C₂, C₃]⟩ },
          { rcases @lambda'_suffix_eq n x μ C₃ with ⟨m, IH₁, IH₂⟩,
            refine ⟨m, nat.lt.step IH₁, IH₂⟩ } } },
      rcases @lambda'_suffix_eq n x μ h with ⟨m, IH₁, IH₂⟩,
      refine ⟨m, nat.lt.step IH₁, IH₂⟩
    end

lemma out_infinity_of_out_inr {η : Tree 0} (υ : branch η → option (Tree 1)) {n : ℕ}
  {μ : branch (lambda' υ n)} {η₀ : Tree 0} (h : out μ = sum.inr η₀) :
  ∃ h : η₀ ⊂ᵢ η, out ⟨η₀, h⟩ = ∞ ∧ υ ⟨η₀, h⟩ = μ.val :=
begin
  have : ∃ m, m < n ∧ lambda' υ m = μ.val ∧ lambda' υ (m + 1) = sum.inr η₀ :: μ.val,
  { simp[out_eq_iff] at h, refine lambda'_suffix_eq υ h },
  rcases this with ⟨m, eqn_m, eqn_μ, eqn_μ'⟩,
  by_cases C₁ : 0 < weight (lambda' υ m) υ; simp[lambda', C₁] at eqn_μ',
  { cases C₂ : is_exists_inv_infinity (lambda' υ m) υ with ν; simp[C₂] at eqn_μ',
    { exfalso, have := list.head_eq_of_cons_eq eqn_μ', simp* at * },
    { have : ν.val = η₀,
        from sum.inr.inj (list.head_eq_of_cons_eq eqn_μ'),
      rcases this with rfl,
      refine ⟨ν.property, _⟩, simp,
      have : out ν = ∞ ∧ υ ν = ↑(lambda' υ m), from out_infinity_of_eq_some υ C₂,
      simp[eqn_μ, this] at* } },
  exfalso, simp[eqn_μ] at eqn_μ', exact eqn_μ'
end

lemma out_infinity_of_out_neq_infinity
  {η : Tree 0} (υ : branch η → option (Tree 1)) {n : ℕ} {μ : branch (lambda' υ n)}
  (h₁ : ∃ η₀ : branch η, υ η₀ = μ.val) (h₂ : ∀ η₀ : branch η, υ η₀ = μ.val → out η₀ ≠ ∞) :
  out μ = ∞ :=
begin
  have : ∃ m, m < n ∧ lambda' υ m = μ.val ∧ lambda' υ (m + 1) = out μ :: μ.val,
    from lambda'_suffix_eq υ (suffix_out_cons μ),
  rcases this with ⟨m, eqn_m, eqn_μ, eqn_μ'⟩,
  have lmm₁ : 0 < weight μ.val υ, from weight_pos_of υ h₁,
  have lmm₂ : is_exists_inv_infinity μ.val υ = none, from eq_none_of_out_neq_infinity υ h₂, simp at*,
  simp[lambda', eqn_μ, lmm₁, lmm₂] at eqn_μ',
  exact eq.symm (list.head_eq_of_cons_eq eqn_μ')
end

lemma out_neq_infinity_of_out_infinity {η : Tree 0} (υ : branch η → option (Tree 1)) {n : ℕ}
  {μ : branch (lambda' υ n)} (h : out μ = ∞) :
  (∃ η₀ : branch η, υ η₀ = μ.val) ∧ (∀ η₀ : branch η, υ η₀ = μ.val → out η₀ ≠ ∞) :=
begin
  have : ∃ m, m < n ∧ lambda' υ m = μ.val ∧ lambda' υ (m + 1) = ∞ :: μ.val,
  { simp[out_eq_iff] at h, exact lambda'_suffix_eq υ h },
  rcases this with ⟨m, eqn_m, eqn_μ, eqn_μ'⟩,
  by_cases C₁ : 0 < weight (lambda' υ m) υ; simp[lambda', C₁] at eqn_μ',
  { cases C₂ : is_exists_inv_infinity (lambda' υ m) υ with ν; simp[C₂] at eqn_μ',
    { simp[←eqn_μ], refine ⟨of_weight_pos υ C₁, out_neq_infinity_of_eq_none υ C₂⟩ },
    { exfalso, have := list.head_eq_of_cons_eq eqn_μ', simp* at* } },
  { exfalso, simp[eqn_μ] at eqn_μ', exact eqn_μ' }
end

def lambda {η : Tree 0} (υ : branch η → option (Tree 1)) : Tree 1 := lambda' υ η.length

def assign {η : Tree 0} (υ : branch η → option (Tree 1)) : Π μ : Tree 1, option (Tree 1 × ℕ)
| []               := none
| (∞ :: μ)        :=
  if h : (assign μ).is_some then S.inf (option.get h) (μ, weight μ υ) else
  some (μ, weight μ υ)
| (sum.inr _ :: μ) := assign μ


def assign_eq {η : Tree 0} (υ : branch η → option (Tree 1)) : Tree 1 → option (Tree 1 × ℕ) := λ μ, assign S υ (∞ :: μ)

def assignment {η : Tree 0} (υ : branch η → option (Tree 1)) : option (Tree 1 × ℕ) := assign_eq S υ (lambda υ)

def up {η : Tree 0} (υ : branch η → option (Tree 1)) : option (Tree 1) := (assignment S υ).map prod.fst

def requirement {η : Tree 0} (υ : branch η → option (Tree 1)) : option R := (assignment S υ).map S.requirement

end approx

def up' (S : strategy R) : Π (η : Tree 0) (μ : branch η), option (Tree 1)
| []       ⟨μ, μ_p⟩ := by exfalso; simp* at*
| (_ :: η) ⟨μ, _⟩   := if h : μ ⊂ᵢ η then up' η ⟨μ, h⟩ else approx.up S (up' η)

def up (η : Tree 0) : option (Tree 1) := approx.up S (up' S η)

lemma up'_up_consistent {η : Tree 0} : ∀ (μ : branch η), S.up' η μ = S.up μ.val :=
begin
  induction η with ν η IH,
  { intros μ, have := μ.property, simp* at* },
  { intros μ, cases μ with μ μ_p, 
    have : μ = η ∨ μ ⊂ᵢ η, from list.is_initial_cons_iff.mp μ_p,
    cases this; simp[this, up'],
    { refl }, { exact IH _ } }
end

def lambda (η : Tree 0) : Tree 1 := approx.lambda (up' S η)

def assignment (η : Tree 0) : option (Tree 1 × ℕ) := approx.assignment S (up' S η)
#check up

@[simp] lemma lambda_nil : S.lambda [] = [] := rfl

lemma out_neq_infinity_of_out_infinity {η : Tree 0} {μ : branch (S.lambda η)}
  (h : out μ = ∞) {η₀ : branch η} (up : S.up η₀.val = μ.val) : out η₀ ≠ ∞ :=
(approx.out_neq_infinity_of_out_infinity (up' S η) h).2 η₀
(by { simp[up'_up_consistent], exact up })

variables (Λ : Tree_path 0)

theorem finite_injury :
  ∀ (n : ℕ), ∃ (s₀ : ℕ), ∀ (s : ℕ), s₀ ≤ s →
    S.lambda (Λ.path s)↾*n = S.lambda (Λ.path s₀)↾*n := λ n,
begin
  induction n with n IH,
  { simp },
  { rcases IH with ⟨s₀, IH⟩,
    suffices :
      ∃ s₁, s₀ ≤ s₁ ∧ ∀ s, s₁ ≤ s → (S.lambda (Λ.path s)).rnth n = (S.lambda (Λ.path s₁)).rnth n,
    { rcases this with ⟨s₁, eqn, hyp_s₁⟩, refine ⟨s₁, λ s eqn_s, _⟩,
      apply list.rnth_ext', { intros m a, simp[list.initial_rnth_some_iff], sorry } },
    by_cases C₁ : ∀ s, list.rnth (S.lambda (Λ.path s)) n = none,
    { refine ⟨s₀, by refl, λ s eqn_s, _⟩, simp[C₁] },
    have C₁ : ∃ (s₁ : ℕ) (ν : infinity ⊕ Tree 0), list.rnth (S.lambda (Λ.path s₁)) n = some ν,
    { simp at C₁, rcases C₁ with ⟨s₁, C₁⟩, have := option.ne_none_iff_exists'.mp C₁, exact ⟨s₁, this⟩ },
    rcases C₁ with ⟨s₁, ν, C₁⟩,
    cases ν,
    { cases ν, refine ⟨max s₀ s₁, by simp, λ s eqn_s, _⟩,
        } }

end 

end strategy


