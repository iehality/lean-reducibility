import lib Tree

open encodable denumerable

attribute [simp] set.set_of_app_iff

universes u v

structure strategy (α : Type u) [decidable_eq α] :=
(par₀ : Tree α 0 → ℕ)
(par₁ : Tree α 1 → ℕ)
(computation : Tree α 0 → option (Tree α 1 × ℕ) → infinity ⊕ Tree' α 0)
(omega_ordering : omega_ordering (Tree α 1 × ℕ))
#check strategy
namespace strategy
variables {α : Type*} [decidable_eq α]
variables (S : strategy α)

namespace approx

def up_inv (η : Tree α 1) {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : list (branch μ) :=
μ.branches.filter (λ a, υ a = η)

lemma up_inv_ordered (η : Tree α 1) {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) :
  (up_inv η υ).ordered (<) :=
by { simp[up_inv], exact list.ordered_filter _ (branch.branches_ordered μ) }

lemma up_inv_cons (η : Tree α 1) {μ : Tree α 0} {x} (υ : branch (x :: μ) → option (Tree α 1)) :
  (up_inv η υ).map subtype.val =
  if υ ⟨μ, by simp⟩ = ↑η
    then μ :: (@up_inv _ _ η μ (λ ν, υ ν.cons')).map subtype.val
    else (@up_inv _ _ η μ (λ ν, υ ν.cons')).map subtype.val :=
begin
  simp[up_inv, list.filter],
  by_cases C : υ ⟨μ, by simp⟩ = ↑η; simp[C],
  { simp[list.map_filter, function.comp], unfold_coes },
  { simp[list.map_filter, function.comp], unfold_coes }
end

lemma up_inv_suffx (η : Tree α 1) {μ₁ μ₂ : Tree α 0} (s : μ₁ ⊆ μ₂)
  (υ₁ : branch μ₁ → option (Tree α 1)) (υ₂ : branch μ₂ → option (Tree α 1))
  (con : ∀ ν₁ : branch μ₁, υ₁ ν₁ = υ₂ (ν₁.extend s)) :
  (up_inv η υ₁).map (branch.extend s) <:+ up_inv η υ₂ :=
begin
  simp[up_inv],
  have : (μ₁.branches.filter (λ a, υ₁ a = ↑η)).map (branch.extend s) =
    (((μ₁.branches).map (branch.extend s)).filter (λ a, υ₂ a = ↑η)),
  { simp[list.map_filter, function.comp, con], unfold_coes, congr },
  rw this, exact (list.is_suffix.filter _ (branch.branches_suffix_of_suffix s))
end

@[simp] lemma up_inv_mem_iff {η : Tree α 1} {μ : Tree α 0} {υ : branch μ → option (Tree α 1)} {μ₀ : branch μ} :
  μ₀ ∈ up_inv η υ ↔ υ μ₀ = η :=
by simp[up_inv]

def weight (η : Tree α 1) {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : ℕ := (up_inv η υ).length

lemma of_pos_weight {η : Tree α 1} {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) (pos : 0 < weight η υ) :
  ∃ μ₀ : branch μ, υ μ₀ = η :=
⟨_, up_inv_mem_iff.mp (list.nth_le_mem _ _ pos)⟩

lemma pos_weight_of {η : Tree α 1} {μ : Tree α 0} (υ : branch μ → option (Tree α 1))
  (h : ∃ μ₀ : branch μ, υ μ₀ = η) : 0 < weight η υ :=
by { rcases h with ⟨μ₀, h⟩, 
     exact list.length_pos_of_mem ((@up_inv_mem_iff _ _ η μ υ μ₀).mpr h) }

lemma le_weight_of_suffix (η : Tree α 1) {μ₁ μ₂ : Tree α 0} (ss : μ₁ <:+ μ₂)
  (υ₁ : branch μ₁ → option (Tree α 1)) (υ₂ : branch μ₂ → option (Tree α 1))
  (con : ∀ ν₁ : branch μ₁, υ₁ ν₁ = υ₂ (ν₁.extend ss)) :
  weight η υ₁ ≤ weight η υ₂ :=
by { have := list.length_le_of_infix (list.infix_of_suffix (up_inv_suffx η ss υ₁ υ₂ con)),
     simp at this, exact this }

def get_up_inv (η : Tree α 1) {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : option (branch μ) :=
(up_inv η υ).get_elem_r (λ μ₀, out μ₀ = ∞)

lemma is_some_of_out_infinity {η : Tree α 1} {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) (μ₀ : branch μ)
  (infty : out μ₀ = ∞) (up : υ μ₀ = η) : (get_up_inv η υ).is_some :=
by { cases C : get_up_inv η υ; simp[get_up_inv, list.get_elem_r_eq_none_iff_mem] at C ⊢,
     exfalso, exact C _ up infty }

lemma get_up_inv_eq_some_iff
  {η : Tree α 1} {μ : Tree α 0} {υ : branch μ → option (Tree α 1)} {μ₀ : branch μ} :
  get_up_inv η υ = ↑μ₀ ↔ (out μ₀ = ∞) ∧ (υ μ₀ = η) ∧ (∀ μ₁, μ₁ < μ₀ → υ μ₁ = η → out μ₁ ≠ ∞) :=
begin
  simp[get_up_inv, list.get_elem_r_eq_some_iff], split,
  { rintros ⟨n, eqn_μ₀, infty₀, min⟩,
    have up₀ : μ₀ ∈ up_inv η υ, from list.mem_iff_rnth.mpr ⟨_, eqn_μ₀⟩, simp at up₀,
    refine ⟨infty₀, up₀, λ μ₁ lt up₁, _⟩,
    have : ∃ n₁, (up_inv η υ).rnth n₁ = ↑μ₁, from list.mem_iff_rnth.mp (up_inv_mem_iff.mpr up₁),
    rcases this with ⟨m, eqn_μ₁⟩,
    have lt : m < n, from (list.ordered_isomorphism (up_inv_ordered η υ) eqn_μ₁ eqn_μ₀).mpr lt,
    exact min _ _ lt eqn_μ₁ },
  { rintros ⟨infty₀, up₀, min⟩, 
    have : ∃ n, (up_inv η υ).rnth n = ↑μ₀,
    { have : μ₀ ∈ up_inv η υ, { simp[up₀] }, exact list.mem_iff_rnth.mp this },
    rcases this with ⟨n, eqn_μ₀⟩,
    refine ⟨n, eqn_μ₀, infty₀, λ m μ₁ eqn_m eqn_μ₁ infty₁, _⟩,
    have lt : μ₁ < μ₀, from list.ordered_mono (up_inv_ordered η υ) eqn_m eqn_μ₁ eqn_μ₀,
    have up : μ₁ ∈ up_inv η υ, from list.mem_iff_rnth.mpr ⟨_, eqn_μ₁⟩, simp at up,
    exact min _ lt up infty₁ }
end

lemma get_up_inv_eq_none_iff {η : Tree α 1} {μ : Tree α 0} {υ : branch μ → option (Tree α 1)} :
  get_up_inv η υ = none ↔ (∀ μ₀ : branch μ, υ μ₀ = η → out μ₀ ≠ ∞) :=
by simp[get_up_inv, list.get_elem_r_eq_none_iff_mem]

lemma get_up_inv_of_suffx (η : Tree α 1) {μ₁ μ₂ : Tree α 0} (ss : μ₁ <:+ μ₂)
  (υ₁ : branch μ₁ → option (Tree α 1)) (υ₂ : branch μ₂ → option (Tree α 1))
  (con : ∀ ν₁ : branch μ₁, υ₁ ν₁ = υ₂ (ν₁.extend ss)) {ν : branch μ₁}
  (h : get_up_inv η υ₁ = some ν) :
  get_up_inv η υ₂ = some (ν.extend ss) :=
begin
  apply get_up_inv_eq_some_iff.mpr,
  have : out ν = ∞ ∧ υ₁ ν = ↑η ∧ ∀ (μ₁' : branch μ₁), μ₁' < ν → υ₁ μ₁' = ↑η → out μ₁' ≠ ∞,
    from get_up_inv_eq_some_iff.mp h,
  rcases this with ⟨out_infty, eqn_up, min⟩,
  have : out ⟨↑ν, list.suffix_of_is_initial_is_initial ν.property ss⟩ = out ν,
    from suffix_out_eq rfl ss,
  refine ⟨by simp[this, out_infty], by simp[con ν] at eqn_up; exact eqn_up, λ μ₂' lt eqn_up' out_infty', _⟩,
  have : out ⟨↑μ₂', list.is_initial.trans lt ν.property⟩ = out μ₂',
    refine eq.symm (suffix_out_eq rfl ss),
  have := min ⟨μ₂', list.is_initial.trans lt ν.property⟩ lt (by simp[con, eqn_up']) (by simp[this, out_infty']),
  contradiction
end

def lambda' {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : ℕ → Tree α 1
| 0       := []
| (n + 1) :=
    if 0 < weight (lambda' n) υ then
      if h : (get_up_inv (lambda' n) υ).is_some then
        sum.inr (option.get h).val :: lambda' n
      else ∞ :: lambda' n
    else lambda' n

def lambda {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : Tree α 1 := lambda' υ μ.length

lemma lambda'_length {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) :
  ∀ n, (lambda' υ n).length ≤ n
| 0       := by simp[lambda']
| (n + 1) :=
    begin
      by_cases C₁ : 0 < weight (lambda' υ n) υ; simp[lambda', C₁],
      { cases C₂ : get_up_inv (lambda' υ n) υ; simp[C₂]; refine lambda'_length n },
      exact le_add_right (lambda'_length n)
    end    
  
lemma lambda'_mono {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : ∀ {n m : ℕ} (le : n ≤ m),
  lambda' υ n ⊆ lambda' υ m :=
begin
  suffices : ∀ n m, lambda' υ n <:+ lambda' υ (n + m),
  { intros n m eqn, have := this n (m - n),
    simp[nat.add_sub_of_le eqn] at this, exact this },
  intros n m, induction m with m IH,
  { refl },
  { simp[←nat.add_one, ←add_assoc, lambda'],
    by_cases C₁ : 0 < weight (lambda' υ (n + m)) υ; simp[C₁],
    { cases C₂ : get_up_inv (lambda' υ (n + m)) υ; simp;
      exact IH.trans (list.suffix_cons _ (lambda' υ (n + m))) },
    exact IH }
end

lemma lambda'_length_mono {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) {n m : ℕ} (le : n ≤ m) :
  (lambda' υ n).length ≤ (lambda' υ m).length :=
list.length_le_of_infix (list.infix_of_suffix (lambda'_mono υ le))

lemma weight0_of_lambda'_length_lt {μ : Tree α 0} {υ : branch μ → option (Tree α 1)} : ∀ {n : ℕ}
 (h : (lambda' υ n).length < n), weight (lambda' υ n) υ = 0
| 0       h := by simp at h; contradiction
| (n + 1) h := by { simp[lambda'] at h ⊢,
    by_cases C : 0 < weight (lambda' υ n) υ; simp[C] at h ⊢,
    { exfalso, cases get_up_inv (lambda' υ n) υ; simp at h ⊢;
      { simp[weight0_of_lambda'_length_lt h] at C, contradiction } },
    { simp at C, exact C } }

lemma constant_of_lambda'_length_lt {μ : Tree α 0} {υ : branch μ → option (Tree α 1)} : ∀ {n m : ℕ} (le : n ≤ m)
  (h : (lambda' υ n).length < n), lambda' υ m = lambda' υ n := 
begin
  suffices : ∀ (n m : ℕ) (h : (lambda' υ n).length < n),
    (lambda' υ (n + m)).length < n + m ∧ lambda' υ (n + m) = lambda' υ n,
  { intros n m eqn h,have := this n (m - n) h,
    simp[nat.add_sub_of_le eqn] at this, exact this.2 },
  intros n m h, induction m with m IH,
  { simp[h] },
  { have : weight (lambda' υ (n + m)) υ = 0, from weight0_of_lambda'_length_lt IH.1,
    simp[←nat.add_one, ←add_assoc, lambda', this],
    refine ⟨nat.lt.step IH.1, IH.2⟩ }
end

lemma length_eq_of_pos_weight {μ : Tree α 0} {υ : branch μ → option (Tree α 1)} {n}
  (h : 0 < weight (lambda' υ n) υ) : (lambda' υ n).length = n :=
begin
  have C : (lambda' υ n).length < n ∨ (lambda' υ n).length = n, from lt_or_eq_of_le (lambda'_length υ n),
  cases C,
  { exfalso,
    have : lambda' υ (n + 1) = lambda' υ n, from constant_of_lambda'_length_lt (by simp) C,
    simp[lambda', h] at this,
    cases C₁ : get_up_inv (lambda' υ n) υ; simp[C₁] at this; contradiction },
    exact C
end

lemma lambda'_suffix_eq {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : ∀ {n : ℕ}
  {x} {η : Tree α 1} (hη : x :: η <:+ lambda' υ n),
  lambda' υ η.length = η ∧ lambda' υ (η.length + 1) = x :: η
| 0       x η h := by { exfalso, simp[lambda', *] at * }
| (n + 1) x η h :=
    begin
      simp[lambda'] at h,
      by_cases C₁ : 0 < weight (lambda' υ n) υ; simp[C₁] at h,
      { have len : (lambda' υ n).length = n, from length_eq_of_pos_weight C₁,
        cases C₂ : get_up_inv (lambda' υ n) υ with ν; simp[C₂] at h,
        { have C₃ : x :: η = ∞ :: lambda' υ n ∨ x :: η <:+ lambda' υ n, from list.suffix_cons_iff.mp h,
          cases C₃,
          { simp at C₃, have : η.length = n, { simp[C₃, len] },
            simp[this, lambda', C₁, C₂], simp[C₃] },
          { exact @lambda'_suffix_eq n x η C₃ } },
        { have C₃ : x :: η = sum.inr ν.val :: lambda' υ n ∨ x :: η <:+ lambda' υ n,
            from list.suffix_cons_iff.mp h,
          cases C₃,
          { simp at C₃, have : η.length = n, { simp[C₃, len] },
            simp[this, lambda', C₁, C₂], simp[C₃] },
          { exact @lambda'_suffix_eq n x η C₃ } } },
      exact @lambda'_suffix_eq n x η h
    end

lemma exists_up_inv {μ : Tree α 0} {υ : branch μ → option (Tree α 1)} {n : ℕ}
  (η₀ : branch (lambda' υ n)) : ∃ μ₀ : branch μ, υ μ₀ = η₀ :=
begin
  have : lambda' υ (list.length ↑η₀) = η₀ ∧ lambda' υ (list.length ↑η₀ + 1) = out η₀ :: η₀.val,
    from lambda'_suffix_eq υ (suffix_out_cons η₀),
  rcases this with ⟨lmm₁, lmm₂⟩,
  simp[lambda', lmm₁] at lmm₂,
  by_cases C : 0 < weight ↑η₀ υ; simp[C] at lmm₂,
  { simp[weight] at C,
    have := up_inv_mem_iff.mp (list.nth_le_mem _ _ C), 
    refine ⟨_, this⟩ },
  { contradiction }
end

lemma branch_of_out_inr {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) {n : ℕ}
  {η : branch (lambda' υ n)} {μ₀ : Tree α 0} (h : out η = sum.inr μ₀) : μ₀ ⊂ᵢ μ :=
begin
  have : lambda' υ (list.length ↑η) = η.val ∧ lambda' υ (list.length ↑η + 1) = sum.inr μ₀ :: η.val,
  { simp[out_eq_iff] at h, refine lambda'_suffix_eq υ h },
  rcases this with ⟨eqn_η, eqn_η'⟩, simp[lambda', eqn_η] at eqn_η',
  by_cases C₁ : 0 < weight ↑η υ; simp[C₁] at eqn_η',
  { cases C₂ : get_up_inv ↑η υ with ν; simp[C₂] at eqn_η',
    { exfalso, have := list.head_eq_of_cons_eq eqn_η', simp* at * },
    { have : ν.val = μ₀,
        from sum.inr.inj (list.head_eq_of_cons_eq eqn_η'),
      rcases this with rfl,
      refine ν.property } },
  contradiction
end

theorem lambda'_convergent_out_iff
  {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) {n : ℕ} {η : branch (lambda' υ n)} {μ₀ : branch μ} :
  out η = sum.inr μ₀.val ↔ (out μ₀ = ∞) ∧ (υ μ₀ = η) ∧ (∀ μ₁, μ₁ < μ₀ → υ μ₁ = η → out μ₁ ≠ ∞) :=
begin
  have : lambda' υ (list.length ↑η) = η ∧ lambda' υ (list.length ↑η + 1) = out η :: η.val,
    from lambda'_suffix_eq υ (suffix_out_cons η),
  rcases this with ⟨eqn_η, eqn_η'⟩, simp[lambda', eqn_η] at eqn_η',
  by_cases C₁ : 0 < weight ↑η υ; simp[C₁] at eqn_η'; simp[eqn_η] at*,
  { cases C₂ : get_up_inv ↑η υ with μ₁; simp[C₂] at eqn_η',
    { have eqn₁ : ∞ = out η, from list.head_eq_of_cons_eq eqn_η', simp[←eqn₁], 
      intros h₁ h₂, exfalso,
      have : ∀ μ₀, υ μ₀ = η → ¬out μ₀ = ∞ := get_up_inv_eq_none_iff.mp C₂,
      exact this _ h₂ h₁ },
    { have eqn₁ : sum.inr μ₁.val = out η, from list.head_eq_of_cons_eq eqn_η',
      have := @get_up_inv_eq_some_iff _ _ ↑η μ υ μ₀,
      simp[←this, C₂, ←eqn₁, ←subtype.ext_iff] } },
  { contradiction }
end

theorem lambda'_divergent_out_iff
  {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) {n : ℕ} {η : branch (lambda' υ n)} :
  out η = ∞ ↔ (∀ μ₀, υ μ₀ = η → out μ₀ ≠ ∞) :=
⟨λ h,
  begin
    have : lambda' υ (list.length ↑η) = η ∧ lambda' υ (list.length ↑η + 1) = out η :: η.val,
      from lambda'_suffix_eq υ (suffix_out_cons η),
    rcases this with ⟨eqn_η, eqn_η'⟩, simp[lambda', eqn_η] at eqn_η',
    by_cases C₁ : 0 < weight ↑η υ; simp[lambda', C₁] at eqn_η',
    { cases C₂ : get_up_inv ↑η υ with ν; simp[C₂] at eqn_η',
      { exact get_up_inv_eq_none_iff.mp C₂ },
      { exfalso, have := list.head_eq_of_cons_eq eqn_η', simp* at* } },
    { contradiction }
  end, λ h,
  begin
    have : lambda' υ (list.length ↑η) = η ∧ lambda' υ (list.length ↑η + 1) = out η :: η.val,
      from lambda'_suffix_eq υ (suffix_out_cons η),
    rcases this with ⟨eqn_η, eqn_η'⟩, simp[lambda', eqn_η] at eqn_η',
    have lmm₁ : 0 < weight η.val υ, from pos_weight_of υ (exists_up_inv η),
    have lmm₂ : get_up_inv η.val υ = none, from get_up_inv_eq_none_iff.mpr h, simp at*,
    simp[lambda', eqn_η, lmm₁, lmm₂] at eqn_η',
    exact eq.symm (list.head_eq_of_cons_eq eqn_η')
  end⟩

private lemma length_le_of_surj {n m : ℕ} {μ : Tree α m} (f : branch μ → option (Tree α n)) {η : Tree α n}
  (h : ∀ η₀ : branch η, ∃ μ₀ : branch μ, f μ₀ = η₀) : η.length ≤ μ.length :=
begin
  have eqn₁ : ((branch.branch_univ μ).image f).card ≤ μ.length,
  { have := @finset.card_image_le _ _ _ f (branch.branch_univ μ), simp at this, exact this },
  have eqn₂ : η.length ≤ ((branch.branch_univ μ).image f).card,
  { have : (branch.branch_univ' η).image option.some ⊆ (branch.branch_univ μ).image f,
    { intros η₀, simp[branch.branch_univ'], rintros η₀ rfl, exact h η₀ },
    have eqn₁ : ((branch.branch_univ' η).image some).card ≤ ((branch.branch_univ μ).image f).card,
      from finset.card_le_of_subset this,
    have eqn₂ : ((branch.branch_univ' η).image some).card = (branch.branch_univ' η).card,
      from finset.card_image_of_injective (branch.branch_univ' η) (option.some_injective (Tree α n)),
    simp at eqn₂, simp [eqn₂] at eqn₁, exact eqn₁ },
  exact le_trans eqn₂ eqn₁
end

lemma lambda_eq_of_le {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : ∀ {n : ℕ} (h : μ.length ≤ n),
  lambda' υ n = lambda υ :=
begin
  suffices :
    ∀ n, lambda' υ (μ.length + n) = lambda υ,
  { intros n eqn, have := this (n - μ.length),
    have eqn : μ.length + (n - μ.length) = n, from nat.add_sub_of_le eqn,
    simp[eqn] at this,
    exact this },
  suffices :
    ¬0 < weight (lambda υ) υ,
  { intros n, induction n with n IH,
    { simp[lambda] }, { simp[←nat.add_one, ←add_assoc, lambda', IH, this] } },
  by_cases C : (lambda υ).length < μ.length,
  { have := weight0_of_lambda'_length_lt C, simp, exact this },
  simp at C,
  intros A,
  have : ∃ (μ₀ : branch μ), υ μ₀ = ↑(lambda υ), from of_pos_weight υ A,
  rcases this with ⟨μ₀, eqn⟩,
  have : ∀ (η₀ : branch (∞ :: (lambda υ))), ∃ (μ₀ : branch μ), υ μ₀ = ↑η₀,
  { intros η₀,
    have : ∀ (η₀ : branch (lambda υ)), ∃ (μ₀ : branch μ), υ μ₀ = ↑η₀, from @exists_up_inv _ _ μ υ μ.length,
    have C₁ : η₀.val = lambda υ ∨ η₀.val ⊂ᵢ lambda υ, from list.is_initial_cons_iff.mp η₀.property,
    cases C₁,
    { exact ⟨μ₀, by simp[eqn, ←C₁]⟩ },
    { exact this ⟨η₀, C₁⟩ } },
  have : (lambda υ).length + 1 ≤ μ.length,
  { have := length_le_of_surj υ this, simp at this, exact this },
  exact ((lambda υ).length).not_succ_le_self (le_trans this C)
end

private lemma lambda'_eq_lambda'_length {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) (n : ℕ) :
  lambda' υ n = lambda' υ (lambda' υ n).length :=
begin
  have le : (lambda' υ n).length ≤ n, from lambda'_length υ n,
  have : (lambda' υ (lambda' υ n).length).length ≤ (lambda' υ n).length,
    from lambda'_length υ (lambda' υ n).length,
  have C := lt_or_eq_of_le this,
  cases C,
  { exact constant_of_lambda'_length_lt le C },
  { exact eq.symm (list.eq_of_suffix_of_length_eq (lambda'_mono υ le) C) }
end 

lemma lambda_eq_of_le' {μ : Tree α 0} {υ : branch μ → option (Tree α 1)} {n : ℕ} (h : (lambda υ).length ≤ n) :
  lambda' υ n = lambda υ :=
begin
  have C : μ.length ≤ n ∨ n ≤ μ.length, from le_total _ _,
  cases C,
  { exact lambda_eq_of_le υ C },
  { have lmm₁ : lambda υ <:+ lambda' υ n,
    { simp[lambda], rw lambda'_eq_lambda'_length υ μ.length, exact lambda'_mono υ h },
    have lmm₂ : lambda' υ n <:+ lambda υ, from lambda'_mono υ C,
    exact list.suffix_antisymm lmm₂ lmm₁ }
end

lemma lambda_initial_eq {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) {n : ℕ} :
  (lambda υ)↾*n = lambda' υ n :=
begin
  have C : (lambda υ).length ≤ n ∨ n < (lambda υ).length, from le_or_lt _ _,
  cases C,
  { simp[list.initial_elim C, lambda_eq_of_le' C] },
  { have : (lambda υ).rnth_le n C :: lambda υ↾*n <:+ lambda υ,
      from list.rnth_eq_iff_suffix_cons_initial.mp (list.rnth_le_rnth C),
    have := lambda'_suffix_eq υ this,
    simp[list.initial_length C] at this, 
    simp[this.1] }
end

lemma up_ne_lambda {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) (μ₀ : branch μ) :
  υ μ₀ ≠ lambda υ := λ up,
begin
  have : lambda υ ⊂ lambda' υ (μ.length + 1),
  { simp[lambda, lambda'],
    have : 0 < weight (lambda' υ μ.length) υ, from pos_weight_of υ ⟨_, up⟩,
    simp[this], cases get_up_inv (lambda' υ μ.length) υ; simp[has_ssubset.ssubset] },
  have eqn : lambda' υ (μ.length + 1) = lambda υ, from lambda_eq_of_le _ μ.length.le_succ,
  simp[eqn, has_ssubset.ssubset] at this,
  contradiction
end

def assign {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) (η : Tree α 1) : option (Tree α 1 × ℕ) :=
S.omega_ordering.Min
  ((η, 0) :: (η.branches.filter (λ μ₀, out μ₀ = ∞)).map (λ η₀ : branch η, (η₀.val, weight η₀.val υ)))

def assignment {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : option (Tree α 1 × ℕ) := assign S υ (lambda υ)

def up {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) : option (Tree α 1) := (assignment S υ).map prod.fst

lemma converge_of_up {μ : Tree α 0} (υ : branch μ → option (Tree α 1)) {η : Tree α 1} 
  (up_μ : up S υ = some η) {μ₀ : branch μ} (up_μ₀ : υ μ₀ = η) : out μ₀ ≠ ∞ := λ div,
begin
  simp[up, assignment, assign, option.map_eq_some'] at up_μ,
  rcases up_μ with ⟨w, up_μ, _⟩,
  rcases up_μ with (⟨rfl, rfl⟩ | ⟨η', div', eqn_η, eqn_w⟩), 
  { have := up_ne_lambda υ μ₀ up_μ₀, contradiction },
  { have : ∀ (μ₀ : branch μ), υ μ₀ = ↑η → ¬out μ₀ = ∞,
    { simp[lambda'_divergent_out_iff, eqn_η] at div', exact div' },
    have := this _ up_μ₀ div, contradiction }
end

end approx

def up' (S : strategy α) : Π (η : Tree α 0) (μ : branch η), option (Tree α 1)
| []       ⟨μ, μ_p⟩ := by exfalso; simp* at*
| (_ :: η) ⟨μ, _⟩   := if h : μ ⊂ᵢ η then up' η ⟨μ, h⟩ else approx.up S (up' η)

def up (η : Tree α 0) : option (Tree α 1) := approx.up S (up' S η)

@[simp] lemma up'_up_consistent {η : Tree α 0} : ∀ (μ : branch η), S.up' η μ = S.up μ.val :=
begin
  induction η with ν η IH,
  { intros μ, have := μ.property, simp* at* },
  { intros μ, cases μ with μ μ_p, 
    have : μ = η ∨ μ ⊂ᵢ η, from list.is_initial_cons_iff.mp μ_p,
    cases this; simp[this, up'],
    { refl }, { exact IH _ } }
end

def lambda' (η : Tree α 0) : ℕ → Tree α 1 := approx.lambda' (S.up' η)

def weight (η : Tree α 1) (μ : Tree α 0) : ℕ := approx.weight η (S.up' μ)

lemma le_weight_of_suffix (η : Tree α 1) {μ₁ μ₂ : Tree α 0} (ss : μ₁ <:+ μ₂) :
  S.weight η μ₁ ≤ S.weight η μ₂ :=
approx.le_weight_of_suffix η ss (S.up' μ₁) (S.up' μ₂) (λ x, by simp)

def lambda (η : Tree α 0) : Tree α 1 := approx.lambda (S.up' η)

lemma lambda'_suffix_eq {μ : Tree α 0} {n : ℕ} {x} {η : Tree α 1} (hη : x :: η <:+ S.lambda' μ n) :
  S.lambda' μ η.length = η ∧ S.lambda' μ (η.length + 1) = x :: η :=
@approx.lambda'_suffix_eq _ _ μ (S.up' μ) n x η hη 

lemma converge_of_up_lt {μ : Tree α 0} {η : Tree α 1} {μ₁ μ₂ : branch μ} (lt : μ₁ < μ₂)
  (up₁ : S.up μ₁ = η) (up₂ : S.up μ₂ = η) : out μ₁ ≠ ∞ :=
by { have out_eqn : out μ₁ = out ⟨↑μ₁, lt⟩, from suffix_out_eq (by simp) (list.suffix_of_is_initial μ₂.property),
     have := @approx.converge_of_up _ _ S μ₂ (S.up' μ₂) _ up₂ ⟨μ₁, lt⟩, simp[←out_eqn] at this,
     exact this up₁ }

lemma converge_of_up {μ : Tree α 0} {η : Tree α 1} 
  (up_μ : S.up μ = η) {μ₀ : branch μ} (up_μ₀ : S.up μ₀ = η) : out μ₀ ≠ ∞ :=
by { have := @approx.converge_of_up _ _ S μ (S.up' μ) η up_μ μ₀, simp at this, exact this up_μ₀ }

lemma lambda'_convergent_out_iff {μ : Tree α 0} {n : ℕ} {η : branch (S.lambda' μ n)} {μ₀ : branch μ} :
  out η = sum.inr μ₀.val ↔ (out μ₀ = ∞) ∧ (S.up μ₀ = η) ∧ (∀ μ₁, μ₁ < μ₀ → S.up μ₁ = η → out μ₁ ≠ ∞) :=
by { have := @approx.lambda'_convergent_out_iff _ _ μ (S.up' μ) n η μ₀, simp at this, 
     exact this }

lemma lambda'_convergent_out_iff' {μ : Tree α 0} {n : ℕ} {η : branch (S.lambda' μ n)} {μ₀ : Tree α 0} :
  out η = sum.inr μ₀ ↔ S.up μ₀ = η ∧ ∃ h : μ₀ ⊂ μ, (out ⟨μ₀, h⟩ = ∞) :=
begin
  have := @approx.lambda'_convergent_out_iff _ _ μ (S.up' μ) n η,
  split,
  { intros h, have lt : μ₀ ⊂ μ, from @approx.branch_of_out_inr _ _ μ (S.up' μ) n η μ₀ h,
    have := (@approx.lambda'_convergent_out_iff _ _ μ (S.up' μ) n η ⟨μ₀, lt⟩).mp h,
    simp[branch.lt_iff] at this, exact ⟨this.2.1, lt, this.1⟩ },
  { rintros ⟨up₀, lt, div⟩, have := (@approx.lambda'_convergent_out_iff _ _ μ (S.up' μ) n η ⟨μ₀, lt⟩).mpr,
    simp only [branch.lt_iff, up'_up_consistent] at this,
    refine this ⟨div, up₀, λ μ₁ lt₀ up₁, _⟩,
    have : out μ₁ = out ⟨↑μ₁, lt₀⟩, from suffix_out_eq (by simp) (list.suffix_of_is_initial lt), simp[this],
    refine S.converge_of_up up₀ up₁ }
end

lemma lambda'_divergent_out_iff
  {μ : Tree α 0} {n : ℕ} {η : branch (S.lambda' μ n)} :
  out η = ∞ ↔ (∀ μ₀ : branch μ, S.up μ₀ = η → out μ₀ ≠ ∞) :=
by { have := @approx.lambda'_divergent_out_iff _ _ μ (S.up' μ) n η, simp at this, 
     exact this }

lemma lambda_initial_eq {μ : Tree α 0} {n : ℕ} : (S.lambda μ)↾*n = S.lambda' μ n :=
@approx.lambda_initial_eq _ _ μ (S.up' μ) n

def assignment (μ : Tree α 0) : option (Tree α 1 × ℕ) := approx.assignment S (up' S μ)

variables (Λ : Path α 0)

lemma pos_of_some_ss {μ₁ μ₂ : Tree α 0} {n : ℕ} {x}
  (ss : μ₁ ⊆ μ₂) (h : (S.lambda μ₁)↾*n = (S.lambda μ₂)↾*n) (d : (S.lambda μ₁).rnth n = some x) :
  0 < S.weight (S.lambda' μ₂ n) μ₂ :=
begin
  have lmm₁ : x :: S.lambda μ₁↾*n <:+ S.lambda μ₁, from rnth_eq_iff_out.mp d,
  have len : (S.lambda μ₁↾*n).length = n, from list.initial_length (list.rnth_some_lt d),
  have h' : S.lambda' μ₁ n = S.lambda' μ₂ n, { simp[S.lambda_initial_eq] at h, exact h },
  have : S.lambda' μ₁ ((S.lambda μ₁↾*n).length + 1) = x :: S.lambda μ₁↾*n, from (S.lambda'_suffix_eq lmm₁).2,
  simp[len, lambda', approx.lambda'] at this,
  by_cases C₁ : 0 < approx.weight (approx.lambda' (S.up' μ₁) n) (S.up' μ₁); simp[C₁] at this,
  { have pos : 0 < S.weight (S.lambda' μ₂ n) μ₁, rw ←h', from C₁,
    have : S.weight (S.lambda' μ₂ n) μ₁ ≤ S.weight (S.lambda' μ₂ n) μ₂,
      from S.le_weight_of_suffix (S.lambda' μ₂ n) ss,
    exact lt_of_lt_of_le pos this },
  { exfalso, have : S.lambda' μ₁ n = x :: S.lambda μ₁↾*n, from this,
    simp[lambda_initial_eq] at this, contradiction }
end

lemma some_of_some_ss (μ₁ μ₂ : Tree α 0) {n : ℕ} {x}
  (ss : μ₁ ⊆ μ₂) (h : (S.lambda μ₁)↾*n = (S.lambda μ₂)↾*n) (d : (S.lambda μ₁).rnth n = some x) :
  ((S.lambda μ₂).rnth n).is_some :=
begin
  have : S.lambda' μ₂ n ⊂ᵢ S.lambda' μ₂ (n + 1),
  { have : 0 < approx.weight (approx.lambda' (S.up' μ₂) n) (S.up' μ₂), from S.pos_of_some_ss ss h d,
    simp[lambda', approx.lambda', this],
    cases C₁ : approx.get_up_inv (approx.lambda' (S.up' μ₂) n) (S.up' μ₂); simp[C₁] },
  have : out ⟨S.lambda μ₂↾*n, _⟩ :: S.lambda μ₂↾*n <:+ S.lambda μ₂↾*(n + 1),
  { have := suffix_out_cons ⟨S.lambda' μ₂ n, this⟩, simp[←lambda_initial_eq] at this, exact this },
  have : list.rnth (S.lambda μ₂) n = some (out ⟨S.lambda μ₂↾*n, _⟩),
    from rnth_eq_iff_out.mpr (this.trans (list.suffix_initial _ _)), 
  simp[this]
end

lemma inr_of_inr_ss (μ₁ μ₂ : Tree α 0) {n : ℕ} {ν : Tree α 0}
  (ss : μ₁ ⊆ μ₂) (h : (S.lambda μ₁)↾*n = (S.lambda μ₂)↾*n) (d : (S.lambda μ₁).rnth n = some (sum.inr ν)) :
  (S.lambda μ₂).rnth n = some (sum.inr ν) :=
begin
  have lmm₁ : sum.inr ν :: S.lambda μ₁↾*n <:+ S.lambda μ₁, from rnth_eq_iff_out.mp d,
  have len : (S.lambda μ₁↾*n).length = n, from list.initial_length (list.rnth_some_lt d),
  have h' : S.lambda' μ₁ n = S.lambda' μ₂ n, { simp[S.lambda_initial_eq] at h, exact h },
  have pos : 0 < approx.weight (approx.lambda' (S.up' μ₂) n) (S.up' μ₂), from S.pos_of_some_ss ss h d,
  have : ∃ h, approx.get_up_inv (S.lambda' μ₂ n) (S.up' μ₂) = some ⟨ν, h⟩,
  { have : S.lambda' μ₁ ((S.lambda μ₁↾*n).length + 1) = sum.inr ν :: S.lambda μ₁↾*n,
      from (S.lambda'_suffix_eq lmm₁).2,
    simp[len, lambda', approx.lambda'] at this,
    by_cases C₁ : 0 < approx.weight (approx.lambda' (S.up' μ₁) n) (S.up' μ₁); simp[C₁] at this,
    { cases C₂ : approx.get_up_inv (approx.lambda' (S.up' μ₁) n) (S.up' μ₁) with ν₂; simp[C₂] at this,
      { exfalso, have := list.head_eq_of_cons_eq this, simp at this, contradiction },
      { have : ↑ν₂ = ν, from sum.inr.inj_iff.mp (list.head_eq_of_cons_eq this), simp[←this],
        have : ν₂.val ⊂ᵢ μ₂, from list.suffix_of_is_initial_is_initial ν₂.property ss,
        refine ⟨this, _⟩, 
        have C₂ : approx.get_up_inv (S.lambda' μ₂ n) (S.up' μ₁) = some ν₂, rw ←h', from C₂,
        exact approx.get_up_inv_of_suffx (S.lambda' μ₂ n) ss (S.up' μ₁) (S.up' μ₂)
          (λ x, by simp) C₂} },
    { exfalso, simp[lambda_initial_eq, lambda'] at this, contradiction } },
  rcases this with ⟨i, eqn⟩,
  have eqn' : approx.get_up_inv (approx.lambda' (S.up' μ₂) n) (S.up' μ₂) = some ⟨ν, i⟩, from eqn,
  cases C : (S.lambda μ₂).rnth n with ν₀,
  { exfalso, have := S.some_of_some_ss _ _ ss h d, simp[C] at this, contradiction },
  have : sum.inr ν :: S.lambda μ₂↾*n <:+ S.lambda μ₂↾*(n + 1),
  { simp[lambda_initial_eq, lambda', approx.lambda'],
    have : 0 < approx.weight (approx.lambda' (S.up' μ₂) n) (S.up' μ₂), from S.pos_of_some_ss ss h d,
    simp[lambda', approx.lambda', this, eqn'] },
  have : list.rnth (S.lambda μ₂) n = some (sum.inr ν),
    from rnth_eq_iff_out.mpr (this.trans (list.suffix_initial _ _)), 
  simp[←C, this] 
end

theorem finite_injury (n : ℕ) :
  ∃ s₀, ∀ s, s₀ ≤ s → S.lambda (Λ.path s)↾*n = S.lambda (Λ.path s₀)↾*n :=
begin
  induction n with n IH,
  { simp },
  { rcases IH with ⟨s₀, IH⟩,
    suffices :
      ∃ s₁, s₀ ≤ s₁ ∧ ∀ s, s₁ ≤ s → (S.lambda (Λ.path s)).rnth n = (S.lambda (Λ.path s₁)).rnth n,
    { rcases this with ⟨s₁, eqn, hyp_s₁⟩, refine ⟨s₁, λ s eqn_s, _⟩,
      apply list.rnth_ext',
      { intros m a, simp[list.initial_rnth_some_iff], intros eqn_m,
        have C : m < n ∨ m = n, from lt_or_eq_of_le (nat.lt_succ_iff.mp eqn_m),
        cases C,
        { have : (S.lambda (Λ.path s)↾*n).rnth m = (S.lambda (Λ.path s₀)↾*n).rnth m,
            from congr_arg (λ l : list _, l.rnth m) (IH s (eqn.trans eqn_s)),
          simp [list.initial_rnth_of_lt C] at this, simp[this],
          have : (S.lambda (Λ.path s₁)↾*n).rnth m = (S.lambda (Λ.path s₀)↾*n).rnth m,
            from congr_arg (λ l : list _, l.rnth m) (IH s₁ eqn),
          simp [list.initial_rnth_of_lt C] at this, simp[this] },
        { simp[C], have := hyp_s₁ s eqn_s, simp[this] } } },
    by_cases C₁ : ∀ s, s₀ ≤ s → (S.lambda (Λ.path s)).rnth n = none,
    { refine ⟨s₀, by refl, λ s eqn_s, _⟩, simp[C₁ s eqn_s, C₁ s₀ (by refl)] },
    have C₁ : ∃ s₁, s₀ ≤ s₁ ∧ ∃ x, (S.lambda (Λ.path s₁)).rnth n = some x,
    { simp at C₁, rcases C₁ with ⟨s₁, eqn, C₁⟩, exact ⟨s₁, eqn, option.ne_none_iff_exists'.mp C₁⟩ },
    rcases C₁ with ⟨s₁, eqn_s₁, ν, C₁⟩,
    by_cases C₂ : ∀ s, s₁ ≤ s → (S.lambda (Λ.path s)).rnth n = some ∞,
    { refine ⟨s₁, eqn_s₁, λ s eqn_s, _⟩, simp[C₂, C₂ s eqn_s] },
    have C₂ : ∃ s₂, s₁ ≤ s₂ ∧ ∃ (ν : Tree α 0), (S.lambda (Λ.path s₂)).rnth n = some (sum.inr ν),
    { simp at C₂, rcases C₂ with ⟨s₂, eqn_s₂, C₂⟩,
      refine ⟨s₂, eqn_s₂, _⟩,
      have : ((S.lambda (Λ.path s₂)).rnth n).is_some,
      { refine S.some_of_some_ss (Λ.path s₁) (Λ.path s₂) (Λ.mono' eqn_s₂) _ C₁,
        { have : S.lambda (Λ.path s₁)↾*n = S.lambda (Λ.path s₀)↾*n, from IH s₁ eqn_s₁, simp[this],
          have : S.lambda (Λ.path s₂)↾*n = S.lambda (Λ.path s₀)↾*n, from IH s₂ (eqn_s₁.trans eqn_s₂),
          simp[this] } },
      have : ∃ x, (S.lambda (Λ.path s₂)).rnth n = some x, from option.is_some_iff_exists.mp this,
      rcases this with ⟨x, eqn_x⟩,
      cases x, { cases x, exfalso, exact C₂ eqn_x },
      refine ⟨x, eqn_x⟩ },
    rcases C₂ with ⟨s₂, eqn_s₂, ν, eqn_ν⟩,
    refine ⟨s₂, eqn_s₁.trans eqn_s₂, λ s eqn_s, _⟩, simp[eqn_ν],
    show (S.lambda (Λ.path s)).rnth n = some (sum.inr ν),
    refine S.inr_of_inr_ss (Λ.path s₂) (Λ.path s) (Λ.mono' eqn_s) _ eqn_ν,
    { have := IH s₂ (eqn_s₁.trans eqn_s₂), simp[this],
      have := IH s ((eqn_s₁.trans eqn_s₂).trans eqn_s), simp[this] } } 
end 

theorem finite_injury' :
  ∃ Λ' : Path α 1, ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → S.lambda (Λ.path s)↾*n = Λ'.path n :=
begin
  let P : ℕ → ℕ → Prop := λ n s₀, (∀ s, s₀ ≤ s → S.lambda (Λ.path s)↾*n = S.lambda (Λ.path s₀)↾*n),
  have : ∀ n, ∃ s₀, P n s₀, from λ n, S.finite_injury Λ n,
  have : ∀ n, ∃ s₀, (∀ s, s < s₀ → ¬P n s) ∧ P n s₀,
  { intros n, exact nat.least_number (this n) },
  have : ∃ (f : ℕ → ℕ), ∀ x, (∀ s, s < f x → ¬P x s) ∧ P x (f x),
    from classical.skolem.mp this,
  rcases this with ⟨f, h_f⟩,
  let path : ℕ → Tree α 1 := λ n, S.lambda (Λ.path (f n))↾*n,
  have mono : ∀ n, path n <:+ path (n + 1),
  { intros n, simp[path],
    have mono : f n ≤ f (n + 1),
    { suffices : ¬f (n + 1) < f n, { simp* at* },
      intros A,
      have min : ∃ x, f (n + 1) ≤ x ∧ ¬S.lambda (Λ.path x)↾*n = S.lambda (Λ.path (f (n + 1)))↾*n,
      { have := (h_f n).1 _ A, simp[P] at this, exact this },
      rcases min with ⟨m, le_m, neq⟩,
      have : S.lambda (Λ.path m)↾*(n + 1) = S.lambda (Λ.path (f (n + 1)))↾*(n + 1),
      { have := (h_f (n + 1)).2 _ le_m, exact this },
      have := (congr_arg (λ l : list _, l↾*n) this), simp at this, exact neq this },
    have : S.lambda (Λ.path (f (n + 1)))↾*n = S.lambda (Λ.path (f n))↾*n, from (h_f n).2 _ mono, 
    simp[←this],
    rw (show S.lambda (Λ.path (f (n + 1)))↾*n = S.lambda (Λ.path (f (n + 1)))↾*(n + 1)↾*n, by simp),
    exact list.suffix_initial _ _ },
  refine ⟨⟨path, mono⟩, λ n, ⟨f n, λ s eqn_s, _⟩⟩,
  exact (h_f n).2 _ eqn_s
end

noncomputable def Lambda (Λ : Path α 0) : Path α 1 := classical.epsilon
(λ Λ',  ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → S.lambda (Λ.path s)↾*n = Λ'.path n)

theorem Lambda_spec : ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → S.lambda (Λ.path s)↾*n = (S.Lambda Λ).path n :=
classical.epsilon_spec (S.finite_injury' Λ)

theorem Lambda_converge {n} {η : branch ((S.Lambda Λ).path n)} {μ : Tree α 0} :
  out η = sum.inr μ ↔ S.up μ = η ∧ ∃ {n} (h : μ ⊂ Λ.path n), out ⟨μ, h⟩ = ∞ :=
begin
    have := S.Lambda_spec Λ n, rcases this with ⟨s₀, h⟩,
  have suf : ∀ {s}, s₀ ≤ s → (S.Lambda Λ).path n <:+ S.lambda (Λ.path s),
    { intros s eqn, simp[←h s eqn], exact list.suffix_initial _ _ },
  have ini : ∀ {s}, s₀ ≤ s → η.val ⊂ S.lambda (Λ.path s),
    from λ s eqn, list.suffix_of_is_initial_is_initial η.property (suf eqn),
  have out_iff : ∀ (s) (eqn : s₀ ≤ s),
    out η = sum.inr μ ↔ S.up μ = ↑η ∧ ∃ (h : μ ⊂ (Λ.path s)), out ⟨μ, h⟩ = ∞,
  { intros s eqn,
    have out_eq : out ⟨η.val, (ini eqn)⟩ = out η, from suffix_out_eq (by simp) (suf eqn),
    have := @lambda'_convergent_out_iff' _ _ S (Λ.path s) _ ⟨η.val, (ini eqn)⟩ μ,
    rw out_eq at this, exact this },
  split,
  { intros h, have := (out_iff s₀ (by simp)).mp h, refine ⟨this.1, s₀, this.2⟩ },
  { rintros ⟨up, s, h, div⟩,
    have lt : μ ⊂ Λ.path (max s s₀), from Λ.ssubset_of_le h (le_max_left s s₀),
    have eqn : out ⟨μ, lt⟩ = out ⟨μ, h⟩, from suffix_out_eq (by simp) (Λ.mono' (le_max_left s s₀)),
    refine (out_iff (max s s₀) (le_max_right s s₀)).mpr ⟨up, lt, by simp[eqn, div]⟩ }
end
 
theorem Lambda_diverge {n} {η : branch ((S.Lambda Λ).path n)} :
  out η = ∞ ↔ ∀ {n} (μ : branch (Λ.path n)), S.up μ = η → out μ ≠ ∞ :=
begin
  have := S.Lambda_spec Λ n, rcases this with ⟨s₀, h⟩,
  have suf : ∀ {s}, s₀ ≤ s → (S.Lambda Λ).path n <:+ S.lambda (Λ.path s),
    { intros s eqn, simp[←h s eqn], exact list.suffix_initial _ _ },
  have ini : ∀ {s}, s₀ ≤ s → η.val ⊂ S.lambda (Λ.path s),
    from λ s eqn, list.suffix_of_is_initial_is_initial η.property (suf eqn),
  have out_iff : ∀ (s) (eqn : s₀ ≤ s),
    out η = ∞ ↔ ∀ (μ₀ : branch (Λ.path s)), S.up ↑μ₀ = ↑η.val → out μ₀ ≠ ∞,
  { intros s eqn,
    have out_eq : out ⟨η.val, (ini eqn)⟩ = out η, from suffix_out_eq (by simp) (suf eqn),
    have := @lambda'_divergent_out_iff _ _ S (Λ.path s) _ ⟨η.val, (ini eqn)⟩,
    rw out_eq at this, exact this },
  split,
  { intros h s μ,
    have lt : μ.val ⊂ Λ.path (max s s₀), from Λ.ssubset_of_le μ.property (le_max_left s s₀),
    have out_eqn : out ⟨↑μ, lt⟩ = out μ, from suffix_out_eq (by simp) (Λ.mono' (le_max_left s s₀)),    
    have := (out_iff (max s s₀) (le_max_right s s₀)).mp h ⟨μ, lt⟩, simp at this,
    simp[out_eqn] at this, exact this },
  { intros h, simp[out_iff s₀ (by simp)], exact @h s₀ }
end

@[simp] def computation_path_aux : ℕ → Tree α 0
| 0       := []
| (s + 1) := S.computation (computation_path_aux s) (S.assignment (computation_path_aux s)) :: computation_path_aux s

def computation_path : Path α 0 := ⟨S.computation_path_aux, by simp⟩

end strategy


