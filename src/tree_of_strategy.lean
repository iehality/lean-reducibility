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

def subTree {n} (η : Tree n) := { μ : Tree n // μ <:+ η ∧ μ ≠ η }

structure Tree_path (n : ℕ) :=
(path : ℕ → Tree n)
(ordered : ∀ m, path m <:+ path (m + 1))

@[simp] lemma list.cons_neq {α : Type*} (a : α) : ∀ (l : list α), l ≠ a :: l
| [] := by simp
| (a₁ :: l) := by { simp, intros h, simp[h], exact list.cons_neq l }


@[simp] lemma list.suffix_cons_append_left {α : Type*} (a : α) : ∀ (l₁ l₂ : list α), ¬ l₁ ++ a :: l₂ <:+ l₂ :=
begin
  intros l₁ l₂, induction l₂ with hd tl IH generalizing l₁ a,
  { simp },
  intros h, have := list.suffix_cons_iff.mp h, cases this,
  { have lmm := (@list.append_left_inj _ (l₁ ++ [a]) [] (hd :: tl)), simp at lmm, exact lmm this },
  { have IH := IH (l₁ ++ [a]) hd, simp at IH, exact IH this }
end

@[simp] lemma list.suffix_cons_left {α : Type*} (a : α) : ∀ (l : list α), ¬ a :: l <:+ l :=
begin
  suffices : ∀ (l₁ l₂ : list α), ¬a :: l₂ ++ l₁ <:+ l₁, { intros l, refine this l [] },
  intros l₁, induction l₁ with hd tl IH,
  { simp },
  intros l₂ h, have := list.suffix_cons_iff.mp h, simp at*, cases this,
  { have lmm := (@list.append_left_inj _ (l₂ ++ [hd]) [] tl), simp at lmm, exact lmm this.2 },
  { have e : a :: (l₂ ++ hd :: tl) = ([a] ++ l₂ ++ [hd]) ++ tl, { simp }, rw e at this,
    refine IH _ this }
end

def subTree.cons' {n} {η : Tree n} {a} (μ : subTree η) : subTree (a :: η) :=
⟨μ.val, ⟨list.suffix_cons_iff.mpr (or.inr μ.property.1), λ h, by { have := μ.property.1, simp[h] at*, exact this }⟩⟩

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

@[reducible] def out {n} (μ η: Tree n) (ν : infinity ⊕ Tree' n) : Prop := ν :: μ <:+ η
notation `out[` η `] ` μ ` ↝ ` ν := out μ η ν

namespace approx

def weight (μ : Tree 1) : Π {η : Tree 0} (υ : subTree η → option (Tree 1)), ℕ
| []       _ := 0
| (_ :: η) υ := @weight η (λ ν, υ ν.cons') + (if υ ⟨η, by simp⟩ = ↑μ then 1 else 0)

def is_exists_inv_infinity (μ : Tree 1) :
  Π {η : Tree 0} (υ : subTree η → option (Tree 1)), option (Tree 0)
| []               _ := none
| (∞ :: η)        υ :=
    if (@is_exists_inv_infinity η (λ ν, υ ν.cons')).is_some then
      @is_exists_inv_infinity η (λ ν, υ ν.cons') else
    if υ ⟨η, by simp⟩ = ↑μ then some η else none
| (sum.inr _ :: η) υ := @is_exists_inv_infinity η (λ ν, υ ν.cons')

lemma out_subtree {n} {η μ : Tree n} {x} (h : out[η] μ ↝ x) : μ <:+ η ∧ μ ≠ η :=
by { simp[out, list.is_suffix] at*, split,
     { rcases h with ⟨ν, ν_p⟩, refine ⟨ν ++ [x], _⟩, simp* at* },
     { intros e, rcases e with rfl, rcases h with ⟨ν, h⟩,
       have := @list.append_left_inj _ (ν ++ [x]) [] μ, simp at this, exact this h } }

lemma is_exists_inv_infinity_infinity (η : Tree 1) (μ : Tree 0) (υ : subTree μ → option (Tree 1)) (μ₀ : subTree μ)
  (h1 : out[μ] μ₀.val ↝ ∞) (h2 : υ μ₀ = η) : (@is_exists_inv_infinity η μ υ).is_some :=
begin
  induction μ with ν μ IH μ IH generalizing μ₀,
  { exfalso, simp[out] at*, exact h1 },
  cases ν,
  { cases ν, simp[is_exists_inv_infinity] at*,
    cases C : (@is_exists_inv_infinity η μ (λ ν, υ ν.cons')).is_some; simp[C],
    { have : ∞ :: μ₀.val = ∞ :: μ ∨ out[μ] μ₀.val ↝ ∞, from list.suffix_cons_iff.mp h1,
      cases this,
      { simp at this, simp[←this, h2] },
      { exfalso, have := IH (λ ν, υ ν.cons') ⟨μ₀.val, out_subtree this⟩ this (by simp[subTree.cons']; exact h2),
        exact bool_iff_false.mpr C this } } },
  { simp[is_exists_inv_infinity],
    have : ∞ :: μ₀.val = sum.inr ν :: μ ∨ out[μ] μ₀.val ↝ ∞, from list.suffix_cons_iff.mp h1,
    cases this,
    { simp at*, exfalso, exact this },
    { simp at*, have := IH (λ ν, υ ν.cons') ⟨μ₀.val, out_subtree this⟩ this (by simp[subTree.cons']; exact h2),
      exact this } }
end

def lambda' {η : Tree 0} (υ : subTree η → option (Tree 1)) : ℕ → Tree 1
| 0       := []
| (n + 1) :=
    if 0 < weight (lambda' n) υ then
      if h : (is_exists_inv_infinity (lambda' n) υ).is_some then
        sum.inr (option.get h) :: lambda' n
      else ∞ :: lambda' n
    else lambda' n 

def lambda {η : Tree 0} (υ : subTree η → option (Tree 1)) : Tree 1 := lambda' υ η.length

def assign {η : Tree 0} (υ : subTree η → option (Tree 1)) : Tree 1 → option (Tree 1 × ℕ)
| []               := none
| (∞ :: μ)        :=
  if h : (assign μ).is_some then S.inf (option.get h) (μ, weight μ υ) else
  some (μ, weight μ υ)
| (sum.inr _ :: μ) := assign μ


def assign_eq {η : Tree 0} (υ : subTree η → option (Tree 1)) : Tree 1 → option (Tree 1 × ℕ) := λ μ, assign S υ (∞ :: μ)

def assignment {η : Tree 0} (υ : subTree η → option (Tree 1)) : option (Tree 1 × ℕ) := assign_eq S υ (lambda υ)

def up {η : Tree 0} (υ : subTree η → option (Tree 1)) : option (Tree 1) := (assignment S υ).map prod.fst

def requirement {η : Tree 0} (υ : subTree η → option (Tree 1)) : option R := (assignment S υ).map S.requirement

end approx

def up' (S : strategy R) : ∀ (η : Tree 0) (μ : subTree η), option (Tree 1)
| []       ⟨μ, μ_p⟩ := by exfalso; simp* at*
| (_ :: η) ⟨μ, μ_p₁, μ_p₂⟩ :=
    have lmm : μ <:+ η,
    { have := list.suffix_cons_iff.mp μ_p₁, cases this,
      { exfalso, exact μ_p₂ this }, { exact this } },
    if h : μ = η then approx.up S (up' η) else up' η ⟨μ, lmm, h⟩

def up (η : Tree 0) : option (Tree 1) := approx.up S (up' S η)

lemma up'_up_consistent {η : Tree 0} : ∀ (μ : subTree η), S.up' η μ = S.up μ.val :=
begin
  induction η with ν η IH,
  { intros μ, have := μ.property, simp* at* },
  { intros μ, cases μ with μ μ_p, rcases μ_p with ⟨μ_p₁, μ_p₂⟩, simp[up', up],
    by_cases C : μ = η; simp[C], { rw [C] }, { simp[IH], refl } }
end

def lambda (η : Tree 0) : Tree 1 := approx.lambda (up' S η)

def assignment (η : Tree 0) : option (Tree 1 × ℕ) := approx.assignment S (up' S η)
#check up

@[simp] lemma lambda_nil : S.lambda [] = [] := rfl

lemma is_exists_inv_infinity_infinity (η : Tree 1) (μ : Tree 0) (μ₀ : Tree 0)
  (h1 : out[μ] μ₀ ↝ ∞) (h2 : S.up μ₀ = η) : out[S.lambda μ] η ↝ sum.inr μ₀ :=
begin
  induction μ with ν μ IH μ IH generalizing μ₀,
  simp,
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


