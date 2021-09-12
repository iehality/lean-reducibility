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

lemma out_cons'_eq {n} {η : Tree n} (ν) (μ : branch η)  :
  @out n (ν :: η) μ.cons' = out μ :=
by { simp[out, branch.cons'], intros h, exfalso, have := h μ.property, exact this }

namespace approx

def weight (μ : Tree 1) : Π {η : Tree 0} (υ : branch η → option (Tree 1)), ℕ
| []       _ := 0
| (_ :: η) υ := @weight η (λ ν, υ ν.cons') + (if υ ⟨η, by simp⟩ = ↑μ then 1 else 0)

def is_exists_inv_infinity (μ : Tree 1) :
  Π {η : Tree 0} (υ : branch η → option (Tree 1)), option (Tree 0)
| []               _ := none
| (sum.inl _ :: η) υ :=
    if (@is_exists_inv_infinity η (λ ν, υ ν.cons')).is_some then
      @is_exists_inv_infinity η (λ ν, υ ν.cons') else
    if υ ⟨η, by simp⟩ = ↑μ then some η else none
| (sum.inr _ :: η) υ := @is_exists_inv_infinity η (λ ν, υ ν.cons')

lemma is_exists_inv_infinity_infinity
  (η : Tree 1) {μ : Tree 0} (υ : branch μ → option (Tree 1)) (μ₀ : branch μ)
  (h1 : out μ₀ = ∞) (h2 : υ μ₀ = η) : (is_exists_inv_infinity η υ).is_some :=
begin
  induction μ with ν μ IH μ IH generalizing μ₀,
  { exfalso, have := μ₀.property, simp* at* },
  have C₁ : μ₀.val = μ ∨ μ₀.val ⊂ᵢ μ, from list.is_initial_cons_iff.mp μ₀.property, cases C₁,
  { cases ν; simp[is_exists_inv_infinity] at*,
    { cases ν,
      cases C₂ : (@is_exists_inv_infinity η μ (λ ν, υ ν.cons')).is_some; simp[C₂],
      { simp[←C₁, h2] } },
    { exfalso, have := out_eq_iff.mp h1, simp[←C₁] at this, exact this } },
  { have IH : (is_exists_inv_infinity η (λ ν, υ ν.cons')).is_some,
      from IH (λ ν, υ ν.cons') ⟨μ₀.val, C₁⟩
        (by {rw ←out_cons'_eq ν ⟨μ₀.val, C₁⟩, simp[branch.cons', h1] })
        (by simp[branch.cons', h2]),
    cases ν; simp[is_exists_inv_infinity] at*; simp[IH] }
end

lemma is_exists_inv_infinity_infinity'
  (η : Tree 1) {μ : Tree 0} (υ : branch μ → option (Tree 1)) (μ₀ : branch μ)
  (h : is_exists_inv_infinity η υ = some μ₀.val) : out μ₀ = ∞ ∧ υ μ₀ = η :=
begin
  induction μ with ν μ IH μ IH generalizing μ₀,
  { exfalso, have := μ₀.property, simp* at* },
  have C₁ : μ₀.val = μ ∨ μ₀.val ⊂ᵢ μ, from list.is_initial_cons_iff.mp μ₀.property, cases C₁,
  { have : μ₀ = ⟨μ, by simp⟩, { apply subtype.ext, exact C₁ },
    rcases this with rfl, 
    cases ν; simp[is_exists_inv_infinity] at*,
    { cases ν,
      cases C₂ : (@is_exists_inv_infinity η μ (λ ν, υ ν.cons')).is_some; simp[C₂] at h,
      { simp[out_eq_iff], exact classical.by_contradiction h },
      { exfalso,   } } }

end

def lambda' {η : Tree 0} (υ : branch η → option (Tree 1)) : ℕ → Tree 1
| 0       := []
| (n + 1) :=
    if 0 < weight (lambda' n) υ then
      if h : (is_exists_inv_infinity (lambda' n) υ).is_some then
        sum.inr (option.get h) :: lambda' n
      else ∞ :: lambda' n
    else lambda' n

def lambda {η : Tree 0} (υ : branch η → option (Tree 1)) : Tree 1 := lambda' υ η.length

def assign {η : Tree 0} (υ : branch η → option (Tree 1)) : Tree 1 → option (Tree 1 × ℕ)
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

lemma is_exists_inv_infinity_infinity (μ : Tree 0) (μ₀ : branch μ) (η : branch (S.lambda μ)) 
  (h1 : out μ₀ = ∞) (h2 : S.up μ₀.val = η.val) : out η = sum.inr μ₀.val :=
begin
  induction μ with ν μ IH μ IH generalizing μ₀; simp[out] at*,
  { exfalso, have := μ₀.property, simp* at* },
  simp[lambda, approx.lambda],
end


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


