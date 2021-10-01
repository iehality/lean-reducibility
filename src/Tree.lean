import lib 

open encodable denumerable

attribute [simp] set.set_of_app_iff

def Tree' : ℕ → Type
| 0       := bool
| (n + 1) := list (Tree' n)

def Tree (n : ℕ) := Tree' (n + 1)

instance : ∀ n, decidable_eq (Tree' n)
| 0       := bool.decidable_eq
| (n + 1) := @list.decidable_eq _ (Tree'.decidable_eq n)

@[simp] def Tree'.proper : ∀ {n}, Tree' n → Prop
| 0       _ := true
| 1       _ := true
| (n + 2) η := list.ordered (⊂ᵢ) η ∧
    ∀ {μ : Tree' (n + 1)}, list.mem μ η → Tree'.proper μ

lemma Tree_aux.proper_of_mem {n} {η : Tree' (n + 1)}
  (proper : η.proper) {μ : Tree' n} (mem : list.mem μ η) : μ.proper :=
by cases n; simp at proper; exact proper.2 mem

lemma Tree_aux.proper_of_cons {n} {η : Tree' (n + 1)} {μ : Tree' n} 
  (proper : @Tree'.proper (n + 1) (list.cons μ η)) : η.proper :=
by cases n; simp at*; refine ⟨list.ordered_cons proper.1, λ ν mem, proper.2 (or.inr mem)⟩

namespace Tree_proper

def nil (k : ℕ) : @Tree'.proper (k + 1) ([] : Tree k) := 
by cases k; simp[list.mem]

def singleton {k : ℕ} (η : Tree' k) (proper : η.proper) : @Tree'.proper (k + 1) [η] :=
by cases k; simp[list.mem, proper]

end Tree_proper

def branch {n} (η : Tree n) := { μ : Tree n // μ ⊂ᵢ η }

instance {n} {η : Tree n} : has_coe (branch η) (Tree n) :=
⟨subtype.val⟩

instance {n} {η : Tree n} : linear_order (branch η) :=
{ le := λ x y, x.val <:+ y.val,
  lt := λ x y, x.val ⊂ᵢ y.val,
  le_refl := λ μ, by simp,
  le_trans := λ μ₁ μ₂ μ₃, list.is_suffix.trans,
  lt_iff_le_not_le := λ μ₁ μ₂, by {
    simp[list.is_initial_iff_suffix], intros h₁,
    split,
    { contrapose, simp, intros h₂, exact list.suffix_antisymm h₁ h₂ },
    { contrapose, simp, intros eqn, simp[eqn] } },
  le_antisymm := λ μ₁ μ₂ eqn₁ eqn₂, subtype.eq (list.suffix_antisymm eqn₁ eqn₂),
  le_total := λ μ₁ μ₂, by { simp[has_le.le, preorder.le],
    have h₁ := (list.is_initial_iff_suffix.mp μ₁.property).1,
    have h₂ := (list.is_initial_iff_suffix.mp μ₂.property).1,
    exact list.suffix_or_suffix_of_suffix h₁ h₂ },
  decidable_le := λ μ₁ μ₂, list.decidable_suffix μ₁.val μ₂.val }

def Tree.branches {n} (η : Tree n) : list (branch η) :=
(list.range_r η.length).pmap (λ m (h :m < η.length), (⟨η↾*m, list.is_initial_of_lt_length h⟩ : branch η))
(λ _, by simp)
-- η.branches = [ ... η↾*2, η↾*1, η↾*0]

namespace branch
variables {k : ℕ}

lemma le_iff {n} {η : Tree n} {μ₁ μ₂ : branch η} : μ₁ ≤ μ₂ ↔ μ₁.val <:+ μ₂.val := by refl

lemma lt_iff {n} {η : Tree n} {μ₁ μ₂ : branch η} : μ₁ < μ₂ ↔ μ₁.val ⊂ᵢ μ₂.val := by refl

def extend {η₁ η₂ : Tree k} (le : η₁ <:+ η₂) (μ : branch η₁) : branch η₂ :=
⟨μ, list.suffix_of_is_initial_is_initial μ.property le⟩

@[simp] lemma extend_val {η₁ η₂ : Tree k} (le : η₁ <:+ η₂) (μ : branch η₁) : 
  (μ.extend le).val = μ := rfl

def extend_fn {α} {η₁ η₂ : Tree k} 
  (f : branch η₂ → α) (le : η₁ <:+ η₂) : branch η₁ → α := λ ν, f (ν.extend le)

@[simp] def extend_fn_val {α} {η₁ η₂ : Tree k}
  (f : branch η₂ → α) (le : η₁ <:+ η₂) (ν : branch η₁) : extend_fn f le ν = f (ν.extend le) := rfl

@[simp] lemma extend_id {n} {η : Tree n} {s} : @extend _ η η s = id :=
funext (by simp[extend])

@[simp] lemma branches_nil {n} : @Tree.branches n [] = [] := rfl

@[simp] lemma branches_cons {n} (η : Tree n) (x) :
  Tree.branches (x :: η) = ⟨η, by simp⟩ :: η.branches.map (extend (by simp)) :=
by { simp[Tree.branches, list.map_pmap], apply list.pmap_congr, simp,
     intros m eqn₁ eqn₂, simp [list.initial_cons eqn₂, extend] }

lemma branches_suffix_of_suffix {n} {μ₁ μ₂ : Tree n} (s : μ₁ <:+ μ₂) :
  μ₁.branches.map (branch.extend s) <:+ μ₂.branches :=
begin
  rcases s with ⟨l, h⟩,
  induction l with x l IH generalizing μ₁ μ₂,
  { simp at h, rcases h with rfl, simp },
  { simp at h, rcases h with rfl, simp,
    have : μ₁.branches.map (λ ν₁, (⟨ν₁.val, _⟩ : branch (x :: (l ++ μ₁))))
      <:+ list.map (extend (list.suffix_cons _ _)) (Tree.branches (l.append μ₁)),
    { have := list.map_suffix (extend (list.suffix_cons _ _)) (@IH μ₁ (l.append μ₁) rfl),
      simp[function.comp] at this, exact this },
    exact this.trans (list.suffix_cons _ _) }
end

@[simp] lemma branches_length {n} {μ : Tree n} : μ.branches.length = μ.length := by simp[Tree.branches]

lemma branches_rnth {n} {μ : Tree n} {i : ℕ} (h : i < μ.length)  :
  μ.branches.rnth i = some ⟨μ↾*i, list.is_initial_of_lt_length h⟩ :=
begin
  have : μ.branches.rnth i = μ.branches.nth (list.length μ - 1 - i),
  { have := @list.rnth_eq_nth_of_lt _ μ.branches i (by simp[h]), simp at this, exact this },
  rw this, simp[Tree.branches, list.nth_pmap],
  refine ⟨i, _, rfl⟩,
  have := @list.rnth_eq_nth_of_lt _ (list.range_r (list.length μ)) i (by simp[h]), simp[h] at this,
  exact eq.symm this
end

lemma branches_ordered {n} : ∀ (μ : Tree n), μ.branches.ordered (<)
| []       := by simp
| (x :: η) := by simp[list.ordered];
    exact ⟨list.ordered_map (extend (by simp)) (λ x y lt, lt) (branches_ordered η), λ η₀ mem, η₀.property⟩

lemma nodup_Tree.branches {n} (η : Tree n) : (Tree.branches η).nodup :=
list.nodup_pmap
  (λ m₁ eqn₁ m₂ eqn₂ eqn, by { simp at eqn, have : (η↾*m₁).length = m₁, from list.initial_length eqn₁,
       simp [eqn, list.initial_length eqn₂] at this, simp[this] })
  (list.nodup_range_r _)

def branch_univ {n} (η : Tree n) : finset (branch η) :=
⟨Tree.branches η, nodup_Tree.branches η⟩

@[simp] lemma branches_complete {n} {η : Tree n} (η₀ : branch η) : η₀ ∈ η.branches :=
list.mem_pmap.2 ⟨η₀.val.length, by { simp[branch_univ],
refine ⟨list.is_initial_length η₀.property, _⟩, apply subtype.ext, simp,
exact list.eq_initial_of_is_initial η₀.property }⟩

@[simp] lemma mem_fin_range {n} {η : Tree n} (η₀ : branch η) : η₀ ∈ branch_univ η :=
branches_complete _

instance {n} (η : Tree n) : fintype (branch η) :=
⟨branch_univ η, mem_fin_range⟩

def branch_univ' {n} (η : Tree n) : finset (Tree n) := (branch_univ η).image subtype.val  

@[simp] lemma branch_univ_card {n} (η : Tree n) : (branch_univ η).card = η.length :=
by simp[branch_univ, Tree.branches]

@[simp] lemma branch_univ'_card {n} (η : Tree n) : (branch_univ' η).card = η.length :=
by { have : (branch_univ' η).card = (branch_univ η).card,
     { apply finset.card_image_of_injective, intros x y, exact subtype.eq },
     simp[this] }

end branch

def out {n} : Π {η : Tree n}, branch η → Tree' n
| []       ⟨μ, μ_p⟩ := by exfalso; simp* at*
| (ν :: η) ⟨μ, μ_p⟩ := if h : μ ⊂ᵢ η then out ⟨μ, h⟩ else ν

lemma out_eq_iff {n} : ∀ {η : Tree n} {μ : branch η} {ν}, out μ = ν ↔ ν :: μ.val <:+ η
| []       ⟨μ, μ_p⟩ _  := by exfalso; simp* at*
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

@[simp] def Tree'.is_pie : Π {k} (η : Tree' k), bool
| 0       ff       := ff
| 0       tt       := tt
| (k + 1) (η :: _) := !Tree'.is_pie η
| (k + 1) []       := ff

@[simp] def Tree'.is_validated : Π {k} (η : Tree' k), bool
| 0       ff       := ff
| 0       tt       := tt
| (k + 1) (η :: _) := Tree'.is_validated η
| (k + 1) []       := ff

def Tree.is_pie {k} (η : Tree' k) : bool := η.is_pie

def branch.pie {k} {η : Tree k} (μ : branch η) : Prop := (out μ).is_pie = tt
def branch.sigma {k} {η : Tree k} (μ : branch η) : Prop := (out μ).is_pie = ff

structure strategy :=
(n : ℕ)
(omega_ordering (k : ℕ) : omega_ordering (Tree k))

namespace strategy
variables (S : strategy)

namespace approx
variables {k : ℕ}

def derivative (η : Tree (k + 1)) {μ : Tree k} (υ : branch μ → option (Tree (k + 1))) : list (branch μ) :=
μ.branches.filter (λ a, υ a = η)

lemma derivative_ordered (η : Tree 1) {μ : Tree 0} (υ : branch μ → option (Tree 1)) :
  (derivative η υ).ordered (<) :=
by simp[derivative]; exact list.ordered_filter _ (branch.branches_ordered μ)

def initial_derivative
  (η : Tree (k + 1)) {μ : Tree k} (υ : branch μ → option (Tree (k + 1))) : option (branch μ) :=
(derivative η υ).nth 0

def pie_derivative
  (η : Tree (k + 1)) {μ : Tree k} (υ : branch μ → option (Tree (k + 1))) : list (branch μ) :=
(derivative η υ).filter (λ μ₀, (out μ₀).is_pie)

def principal_derivative
  (η : Tree (k + 1)) {μ : Tree k} (υ : branch μ → option (Tree (k + 1))) : option (branch μ) :=
((pie_derivative η υ).nth 0).cases_on' (initial_derivative η υ) some

def lambda : ∀ {μ : Tree k} (υ : branch μ → option (Tree (k + 1))), Tree (k + 1)
| []       _ := []
| (x :: μ) υ := let ih := lambda (@branch.extend_fn k _ μ _ υ (by simp)) in 
    if ∃ h : (υ ⟨μ, by simp⟩).is_some, (option.get h = ih) ∨
      (x.is_pie = tt ∧ pie_derivative (option.get h) υ = [])
    then (x :: μ) :: ih
    else ih

def antiderivative {μ : Tree k} (υ : branch μ → option (Tree (k + 1))) : option (Tree (k + 1)) :=
(S.omega_ordering (k + 1)).Min (lambda υ :: ((lambda υ).branches.filter (λ μ₀, (out μ₀).is_pie)).map subtype.val)


end approx


end strategy


