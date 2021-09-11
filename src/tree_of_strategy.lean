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
| (n + 1) := list (Tree' n ⊕ infinity)

instance : ∀ n, decidable_eq (Tree' n)
| 0       := zero.decidable_eq
| (n + 1) := @list.decidable_eq _ (@sum.decidable_eq _ (Tree'.decidable_eq n) infinity _)

def Tree (n : ℕ) := Tree' (n + 1)

def subTree {n} (η : Tree n) := { μ : Tree n // μ <:+ η }

instance : has_zero (zero ⊕ infinity) := ⟨sum.inl zero.zero⟩
instance {n} : has_emptyc (Tree n) := ⟨[]⟩

notation `∞` := sum.inr infinity.infinity


#check @list.rec_on



@[elab_as_eliminator]
theorem Tree'.rec_on {n} {motive : Tree' (n+1) → Sort*} (μ : Tree' (n + 1))
  (nil : motive [])
  (cons₁ : Π (ν : Tree' n) (μ : Tree' (n + 1)), motive μ → motive (sum.inl ν :: μ))
  (cons₂ : Π (μ : Tree' (n + 1)), motive μ → motive (∞ :: μ)) : motive μ :=
begin
  induction μ with ν μ IH, refine nil,
  cases ν, { refine cons₁ ν μ IH },
  { cases ν, refine cons₂ μ IH }
end

@[elab_as_eliminator]
theorem Tree.rec_on {n} {motive : Tree (n+1) → Sort*} (μ : Tree (n + 1))
  (nil : motive [])
  (cons₁ : Π (ν : Tree n) (μ : Tree (n + 1)), motive μ → motive (sum.inl ν :: μ))
  (cons₂ : Π (μ : Tree (n + 1)), motive μ → motive (∞ :: μ)) : motive μ :=
@Tree'.rec_on (n + 1) motive μ nil cons₁ cons₂

@[elab_as_eliminator]
theorem Tree'.rec_on₁ {motive : Tree 1 → Sort*} (μ : Tree 1) 
  (nil : motive (∅ : Tree 1))
  (cons₁ : Π (ν : Tree 0) (μ : Tree 1), motive μ → motive (sum.inl ν :: μ))
  (cons₂ : Π (μ : Tree 1), motive μ → motive (∞ :: μ : Tree 1)) : motive μ :=
@Tree'.rec_on 1 motive μ nil cons₁ cons₂

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

@[reducible] def out {n} (μ η: Tree n) (ν : Tree' n ⊕ infinity) : Prop := ν :: μ <:+ η
notation `out[` η `] ` μ ` ↝ ` ν := out μ η ν

namespace approx
variables υ : Π (n : ℕ) (η : Tree 0) (h : η.length < n), option (Tree 1)

def weight (μ : Tree 1) : Π (η : Tree 0) (υ : subTree η → option (Tree 1)), ℕ
| []       _ := 0
| (_ :: η) υ := weight η (λ ν, υ ⟨ν.val, list.suffix_cons_iff.mpr(or.inr ν.property)⟩) +
  (if υ ⟨η, by simp⟩ = ↑μ then 1 else 0)

/--
def weight (η : Tree 1) : Tree 0 → ℕ
| []       := 0
| (_ :: μ) := weight μ + (if υ μ = ↑η then 1 else 0)
-/

def is_exists_inv_infinity (η : Tree 1) : Tree 0 → option (Tree 0)
| []               := none
| (sum.inl _ :: μ) := is_exists_inv_infinity μ
| (∞ :: μ)        :=
    if (is_exists_inv_infinity μ).is_some then is_exists_inv_infinity μ
    else if υ μ = ↑η then some μ else none

lemma is_exists_inv_infinity_infinity (η : Tree 1) (μ : Tree 0) {μ₀ : Tree 0}
  (h1 : out[μ] μ₀ ↝ ∞) (h2 : υ μ₀ = η) : (is_exists_inv_infinity υ η μ).is_some :=
begin
  induction μ with ν μ IH μ IH generalizing μ₀,
  { exfalso, simp[out] at*, exact h1 },
  cases ν,
  { simp[is_exists_inv_infinity],
    have : ∞ :: μ₀ = sum.inl ν :: μ ∨ out[μ] μ₀ ↝ ∞, from list.suffix_cons_iff.mp h1,
    cases this,
    { simp at*, exfalso, exact this },
    { refine IH this h2 } },
  { cases ν, simp[is_exists_inv_infinity] at*,
    cases C : (is_exists_inv_infinity υ η μ).is_some; simp[C],
    { have : ∞ :: μ₀ = ∞ :: μ ∨ out[μ] μ₀ ↝ ∞, from list.suffix_cons_iff.mp h1,
      cases this,
      { simp at*, rcases this with rfl, simp[h2] },
      { exfalso, have := IH this h2, exact bool_iff_false.mpr C this } } }
end

def lambda' (η : Tree 0) : ℕ → Tree 1
| 0       := []
| (n + 1) :=
    if 0 < weight υ (lambda' n) η then
      if h : (is_exists_inv_infinity υ (lambda' n) η).is_some then
        sum.inl (option.get h) :: lambda' n
      else ∞ :: lambda' n
    else lambda' n 

def lambda (η : Tree 0) : Tree 1 := lambda' υ η η.length

def assign (η : Tree 0) : Tree 1 → option (Tree 1 × ℕ)
| []               := none
| (sum.inl _ :: μ) := assign μ
| (∞ :: μ)        :=
  if h : (assign μ).is_some then S.inf (option.get h) (μ, weight υ μ η) else
  some (μ, weight υ μ η)

def assign_eq (η : Tree 0) : Tree 1 → option (Tree 1 × ℕ) := λ μ,
if h : (assign S υ η μ).is_some then S.inf (option.get h) (μ, weight υ μ η) else
  some (μ, weight υ μ η)

def up (η : Tree 0) : option (Tree 1 × ℕ) := assign_eq S υ η (lambda υ η)

def requirement (η : Tree 0) : option R := (up S υ η).map S.requirement

end approx

def up : Tree 0 → option (Tree 1 × ℕ)
| [] 



end strategy


