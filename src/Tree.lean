import reducibility function  data.list.basic

open encodable denumerable t_reducible

attribute [simp] set.set_of_app_iff

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

def branch {n} (η : Tree n) := { μ : Tree n // μ ⊂ᵢ η }

instance {n} {η : Tree n} : has_lt (branch η) := ⟨λ x y, x.val ⊂ᵢ y.val⟩
instance {n} {η : Tree n} : has_le (branch η) := ⟨λ x y, x.val <:+ y.val⟩

instance {n} : has_ssubset (Tree n) := ⟨λ x y, x ⊂ᵢ y⟩
instance {n} : has_subset (Tree n) := ⟨λ x y, x <:+ y⟩

namespace branch

def branch_range {n} (η : Tree n) : list (branch η) :=
(list.range η.length).pmap (λ m (h :m < η.length), ⟨η↾*m, list.is_initial_of_lt_length h⟩) (λ _, by simp)

lemma nodup_branch_range {n} (η : Tree n) : (branch_range η).nodup :=
list.nodup_pmap
  (λ m₁ eqn₁ m₂ eqn₂ eqn, by { simp at eqn, have : (η↾*m₁).length = m₁, from list.initial_length eqn₁,
       simp [eqn, list.initial_length eqn₂] at this, simp[this] })
  (list.nodup_range _)

def branch_univ {n} (η : Tree n) : finset (branch η) :=
⟨branch_range η, nodup_branch_range η⟩

@[simp] lemma mem_fin_range {n} {η : Tree n} (η₀ : branch η) : η₀ ∈ branch_univ η :=
list.mem_pmap.2 ⟨η₀.val.length, by { simp[branch_univ],
refine ⟨list.is_initial_length η₀.property, _⟩, apply subtype.ext, simp,
exact list.eq_initial_of_is_initial η₀.property }⟩

instance {n} (η : Tree n) : fintype (branch η) :=
⟨branch_univ η, mem_fin_range⟩

def branch_univ' {n} (η : Tree n) : finset (Tree n) := (branch_univ η).image subtype.val  

@[simp] lemma branch_univ_card {n} (η : Tree n) : (branch_univ η).card = η.length :=
by simp[branch_univ, branch_range]

@[simp] lemma branch_univ'_card {n} (η : Tree n) : (branch_univ' η).card = η.length :=
by { have : (branch_univ' η).card = (branch_univ η).card,
     { apply finset.card_image_of_injective, intros x y, exact subtype.eq },
     simp[this] }

instance {n} {η : Tree n} : has_coe (branch η) (Tree n) :=
⟨subtype.val⟩

lemma linear {n} {η : Tree n} {μ₁ μ₂ : branch η} :
  μ₂ ≤ μ₁ ↔ ¬μ₁ < μ₂ :=
begin
  split,
  { simp[has_lt.lt, has_le.le, list.suffix_iff_is_initial], rintros (h | h),
    { intros h₁, have := h.trans h₁, simp* at* },
    { simp[h] } },
  { simp[has_lt.lt, has_le.le, list.is_initial_iff_suffix], intros h,
    rcases list.is_initial_iff_suffix.mp μ₁.property with ⟨h₁, eqn₁⟩,
    rcases list.is_initial_iff_suffix.mp μ₂.property with ⟨h₂, eqn₂⟩,
    have : μ₁.val <:+ μ₂.val ∨ μ₂.val <:+ μ₁.val, from list.suffix_or_suffix_of_suffix h₁ h₂,
    cases this,
    { simp[h this] }, { exact this } }
end

lemma le_lt {n} {η : Tree n} {μ₁ μ₂ : branch η} :
  μ₁ ≤ μ₂ ↔ μ₁ < μ₂ ∨ μ₁ = μ₂ :=
by { simp[has_lt.lt, has_le.le],
     have := @list.suffix_iff_is_initial _ (↑μ₁) (↑μ₂), rw [←subtype.ext_iff] at this,
     exact this }

end branch

structure Path (n : ℕ) :=
(path : ℕ → Tree n)
(mono : ∀ m, path m <:+ path (m + 1))

namespace Path

variables {i : ℕ} (Λ : Path i)

lemma mono' : ∀ {n m : ℕ} (le : n ≤ m), Λ.path n <:+ Λ.path m :=
begin
  suffices : ∀ n m, Λ.path n <:+ Λ.path (n + m),
  { intros n m eqn, have := this n (m - n), simp[nat.add_sub_of_le eqn] at this,
    exact this },
  intros n m, induction m with m IH,
  { refl },
  { simp[←nat.add_one, ←add_assoc], exact IH.trans (Λ.mono _) }
end

end Path

def branch.cons' {n} {η : Tree n} {a} (μ : branch η) : branch (a :: η) :=
⟨μ.val, μ.property.trans (η.is_initial_cons _)⟩

instance : has_zero (zero ⊕ infinity) := ⟨sum.inl zero.zero⟩

notation `∞` := sum.inl infinity.infinity
