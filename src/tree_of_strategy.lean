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

lemma branch_linear {n} {η : Tree n} {μ₁ μ₂ : branch η} :
  μ₂.val <:+ μ₁.val ↔ ¬μ₁.val ⊂ᵢ μ₂.val :=
begin
  split,
  { simp[list.suffix_iff_is_initial], rintros (h | h),
    { intros h₁, have := h.trans h₁, simp* at* },
    { simp[h] } },
  { simp[list.is_initial_iff_suffix], intros h,
    rcases list.is_initial_iff_suffix.mp μ₁.property with ⟨h₁, eqn₁⟩,
    rcases list.is_initial_iff_suffix.mp μ₂.property with ⟨h₂, eqn₂⟩,
    have : μ₁.val <:+ μ₂.val ∨ μ₂.val <:+ μ₁.val, from list.suffix_or_suffix_of_suffix h₁ h₂,
    cases this,
    { simp[h this] }, { exact this } }
end

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

lemma out_cons'_eq' {n} {η : Tree n} (ν) (μ : branch η) {h : μ.val ⊂ᵢ ν :: η} :
  @out n (ν :: η) ⟨μ.val, h⟩ = out μ :=
by { simp[out, branch.cons'], intros h, exfalso, have := h μ.property, exact this }

lemma suffix_out_eq {n} : ∀ {η₁ η₂: Tree n} {μ₁ : branch η₁} {μ₂ : branch η₂}
  (h₁ : μ₁.val = μ₂.val) (h₂ : η₂ <:+ η₁), out μ₁ = out μ₂ :=
begin
  suffices : ∀ (l : list _) {η₁ η₂: Tree n} {μ₁ : branch η₁} {μ₂ : branch η₂}
    (h₁ : μ₁.val = μ₂.val) (h₂ : l.reverse ++ η₂ = η₁), out μ₁ = out μ₂,
  { intros η₁ η₂ μ₁ μ₂ h₁ h₂, rcases h₂ with ⟨l, h₂⟩,
    exact this l.reverse h₁ (by simp[h₂]) },
  intros l η₁ η₂ μ₁ μ₂ h₁ h₂,
  induction l with ν l IH generalizing η₁ η₂,
  { simp at h₂, rcases h₂ with rfl, congr, exact subtype.eq h₁ },
  { simp at h₂,
    let μ₂' : branch (ν :: η₂) := ⟨μ₂.val, μ₂.property.trans (by simp)⟩,
    have h₁' : μ₁.val = μ₂'.val, { simp[μ₂', h₁] },
    have eqn₁ : out μ₁ = out μ₂', from IH h₁' h₂,
    have eqn₂ : out μ₂' = out μ₂, from out_cons'_eq' ν μ₂,
    simp[eqn₁, eqn₂] }
end

lemma rnth_eq_iff_out {n} {η : Tree n} {μ : branch η} {ν} {m : ℕ} :
  η.rnth m = some ν ↔ ν :: η↾*m <:+ η :=
list.rnth_eq_iff_suffix_cons_initial

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

def get_inv_up (μ : Tree 1) :
  Π {η : Tree 0} (υ : branch η → option (Tree 1)), option (branch η)
| []               _ := none
| (sum.inl _ :: η) υ :=
    if (@get_inv_up η (λ ν, υ ν.cons')).is_some then
      (@get_inv_up η (λ ν, υ ν.cons')).map branch.cons' else
    if υ ⟨η, by simp⟩ = ↑μ then some ⟨η, by simp⟩ else none
| (sum.inr _ :: η) υ := (@get_inv_up η (λ ν, υ ν.cons')).map branch.cons'

lemma is_some_of_out_infinity {η : Tree 1} :
  ∀ {μ : Tree 0} (υ : branch μ → option (Tree 1)) (μ₀ : branch μ)
  (h1 : out μ₀ = ∞) (h2 : υ μ₀ = η), (get_inv_up η υ).is_some 
| []       υ μ₀ _  _  := by { exfalso, have := μ₀.property, simp* at*  }
| (ν :: μ) υ μ₀ h1 h2 :=
    begin
      have C₁ : μ₀.val = μ ∨ μ₀.val ⊂ᵢ μ, from list.is_initial_cons_iff.mp μ₀.property, cases C₁,
      { cases ν; simp[get_inv_up] at*,
        { cases ν,
          cases C₂ : @get_inv_up η μ (λ ν, υ ν.cons'); simp[C₂],
          { simp[←C₁, h2] } },
        { exfalso, have := out_eq_iff.mp h1, simp[←C₁] at this, exact this } },
      { have IH : (get_inv_up η (λ ν, υ ν.cons')).is_some,
          from @is_some_of_out_infinity μ (λ ν, υ ν.cons') ⟨μ₀.val, C₁⟩
        (by {rw ←out_cons'_eq ν ⟨μ₀.val, C₁⟩, simp[branch.cons', h1] })
        (by simp[branch.cons', h2]),
        cases ν; simp[get_inv_up] at*; 
        rcases option.is_some_iff_exists.mp IH with ⟨_, IH⟩; simp[IH] }
    end

lemma out_infinity_of_eq_some {η : Tree 1} :
  ∀ {μ : Tree 0} (υ : branch μ → option (Tree 1)) {μ₀ : branch μ}
  (h : get_inv_up η υ = some μ₀), out μ₀ = ∞ ∧ υ μ₀ = η
| []               _ μ₀ _ := by { exfalso, have := μ₀.property, simp* at* }
| (∞ :: μ)        υ μ₀ h :=
    begin
      cases C₁ : (@get_inv_up η μ (λ ν, υ ν.cons')).is_some;
      simp[get_inv_up, C₁] at h,
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
      simp[get_inv_up] at h,
      rcases h with ⟨μ₁, h, eqn⟩,
        have IH : out μ₁ = ∞ ∧ υ μ₁.cons' = ↑η,
          from @out_infinity_of_eq_some _ (λ ν, υ ν.cons') μ₁ h,
      simp[←eqn, out_cons'_eq], exact IH
    end

lemma get_inv_up_eq_some_of_eq_some (η : Tree 1) :
  ∀ {μ : Tree 0} (υ : branch μ → option (Tree 1)) {μ₀ : branch μ} {μ₁ : branch μ₀.val}
  (h : @get_inv_up η μ₀.val (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩) = some μ₁),
  get_inv_up η υ = some ⟨μ₁.val, μ₁.property.trans μ₀.property⟩
| []       _ μ₀ _  _ := by { exfalso, have := μ₀.property, simp* at* }
| (ν :: μ) υ μ₀ μ₁ h := 
    begin
      have C₁ : μ₀.val = μ ∨ μ₀.val ⊂ᵢ μ, from list.is_initial_cons_iff.mp μ₀.property, cases C₁,
      { have : μ₀ = ⟨μ, by simp⟩, from subtype.ext_val C₁, rcases this with rfl,
        { have : get_inv_up η (λ ν, υ ν.cons') = some μ₁, from h,
          cases ν; simp[get_inv_up, this, h]; refl } },
      have := @get_inv_up_eq_some_of_eq_some μ (λ ν, υ ν.cons') ⟨μ₀.val, C₁⟩ μ₁ h, 
      cases ν; simp[get_inv_up, this, h]; refl
    end

private lemma get_inv_up_eq_none_of_eq_some {η : Tree 1} {μ : Tree 0} (υ : branch μ → option (Tree 1)) {μ₀ : branch μ}
  (h : get_inv_up η υ = ↑μ₀) :
  @get_inv_up η μ₀.val (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩) = none :=
begin
  cases C : @get_inv_up η μ₀.val (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩) with μ₁,
  { refl },
  exfalso,
  have : get_inv_up η υ = some ⟨μ₁.val, _⟩, from get_inv_up_eq_some_of_eq_some η υ C,
  have eqn : μ₁.val = μ₀.val, { simp[this] at h, exact congr_arg subtype.val (option.some_inj.mp h) },
  have : μ₁.val ⊂ᵢ μ₀.val, from μ₁.property, 
  simp [eqn] at this, exact this
end

lemma get_inv_up_iff
  {η : Tree 1} {μ : Tree 0} (υ : branch μ → option (Tree 1)) {μ₀ : branch μ} :
  (out μ₀ = ∞) ∧ (υ μ₀ = η) ∧ (∀ μ₁ : branch μ, out μ₁ = ∞ → υ μ₁ = η → μ₀.val <:+ μ₁.val) ↔
  get_inv_up η υ = ↑μ₀ :=
⟨λ ⟨h₁, h₂, h₃⟩,
  begin
    have : ∃ (μ₁ : branch μ), get_inv_up η υ = some μ₁,
      from option.is_some_iff_exists.mp (is_some_of_out_infinity υ μ₀ h₁ h₂),
    rcases this with ⟨μ₁, h_μ₁⟩,
    have : out μ₁ = ∞ ∧ υ μ₁ = ↑η, from out_infinity_of_eq_some υ h_μ₁,
    have lmm : μ₀.val <:+ μ₁.val := h₃ μ₁ this.1 this.2,
    suffices : ¬ μ₀.val ⊂ᵢ μ₁.val,
    { have : μ₀ = μ₁, from subtype.eq (list.suffix_antisymm lmm (branch_linear.mpr this)),
      rw [this], exact h_μ₁ },
    intros A,
    have eqn : @get_inv_up η μ₁.val (λ x, υ ⟨x.val, x.property.trans μ₁.property⟩) = none,
      from get_inv_up_eq_none_of_eq_some υ h_μ₁,
    have : (@get_inv_up η μ₁.val (λ x, υ ⟨x.val, x.property.trans μ₁.property⟩)).is_some,
    { have : out μ₀ = out ⟨μ₀.val, A⟩,
        from @suffix_out_eq _ _ _ μ₀ ⟨μ₀.val, A⟩ rfl (list.suffix_of_is_initial μ₁.property),
      refine is_some_of_out_infinity (λ x, υ ⟨x.val, x.property.trans μ₁.property⟩)
      ⟨μ₀.val, A⟩ (by rw[←this, h₁]) (by simp; exact h₂) },
    rw[eqn] at this, exact option.not_is_some_iff_eq_none.mpr rfl this
  end, λ h,
  begin
    have := out_infinity_of_eq_some υ h,
    refine ⟨this.1, this.2, λ μ₁ h₁ h₂, _⟩,
    suffices : ¬ μ₁.val ⊂ᵢ μ₀.val,
    { exact branch_linear.mpr this }, intros A,    
    have eqn : @get_inv_up η μ₀.val (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩) = none,
      from get_inv_up_eq_none_of_eq_some υ h,
    have : (@get_inv_up η μ₀.val (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩)).is_some,
    { have : out μ₁ = out ⟨μ₁.val, A⟩,
        from @suffix_out_eq _ _ _ μ₁ ⟨μ₁.val, A⟩ rfl (list.suffix_of_is_initial μ₀.property),
      refine is_some_of_out_infinity (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩)
      ⟨μ₁.val, A⟩ (by rw[←this, h₁]) (by simp; exact h₂) },
    rw eqn at this, exact option.not_is_some_iff_eq_none.mpr rfl this
  end⟩

lemma out_neq_infinity_of_eq_none {η : Tree 1}
  {μ : Tree 0} (υ : branch μ → option (Tree 1))
  (h : get_inv_up η υ = none) (μ₀ : branch μ) : υ μ₀ = η → out μ₀ ≠ ∞ :=
begin
  by_cases C : υ μ₀ = ↑η ∧ out μ₀ = ∞,
  { exfalso, have := is_some_of_out_infinity υ μ₀ C.2 C.1, simp[h] at this, exact this },
  { simp at C, exact C }
end

lemma eq_none_of_out_neq_infinity {η : Tree 1} :
  ∀ {μ : Tree 0} (υ : branch μ → option (Tree 1))
  (h : ∀ μ₀ : branch μ, υ μ₀ = η → out μ₀ ≠ ∞), get_inv_up η υ = none
| []       _ _ := by simp[get_inv_up]
| (ν :: μ) υ h :=
    begin
      have : ∀ (μ₀ : branch μ), υ μ₀.cons' = ↑η → out μ₀ ≠ ∞,
        { intros μ₀, simp[←out_cons'_eq ν μ₀, branch.cons'],
          have := h ⟨μ₀.val, μ₀.property.trans (μ.is_initial_cons _)⟩, exact this }, 
        have : get_inv_up η (λ ν, υ ν.cons') = none,
          from eq_none_of_out_neq_infinity (λ ν, υ ν.cons') this,
        cases ν; simp[get_inv_up, this],
        { cases ν, intros hμ,
          have : out ⟨μ, _⟩ ≠ ∞ := h ⟨μ, by simp⟩ hμ,
          simp[out_eq_iff] at this, exact this }
    end

def lambda' {η : Tree 0} (υ : branch η → option (Tree 1)) : ℕ → Tree 1
| 0       := []
| (n + 1) :=
    if 0 < weight (lambda' n) υ then
      if h : (get_inv_up (lambda' n) υ).is_some then
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
      { cases C₂ : (get_inv_up (lambda' υ n) υ).is_some; simp[C₂] at h,
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
  { cases C₂ : get_inv_up (lambda' υ m) υ with ν; simp[C₂] at eqn_μ',
    { exfalso, have := list.head_eq_of_cons_eq eqn_μ', simp* at * },
    { have : ν.val = η₀,
        from sum.inr.inj (list.head_eq_of_cons_eq eqn_μ'),
      rcases this with rfl,
      refine ⟨ν.property, _⟩, simp,
      have : out ν = ∞ ∧ υ ν = ↑(lambda' υ m), from out_infinity_of_eq_some υ C₂,
      simp[eqn_μ, this] at* } },
  exfalso, simp[eqn_μ] at eqn_μ', exact eqn_μ'
end

lemma out_neq_infinity_iff_out_infinity
  {η : Tree 0} (υ : branch η → option (Tree 1)) {n : ℕ} {μ : branch (lambda' υ n)} :
  (∃ η₀ : branch η, υ η₀ = μ.val) ∧ (∀ η₀ : branch η, υ η₀ = μ.val → out η₀ ≠ ∞) ↔ out μ = ∞ :=
⟨λ ⟨h₁, h₂⟩, begin
    have : ∃ m, m < n ∧ lambda' υ m = μ.val ∧ lambda' υ (m + 1) = out μ :: μ.val,
      from lambda'_suffix_eq υ (suffix_out_cons μ),
    rcases this with ⟨m, eqn_m, eqn_μ, eqn_μ'⟩,
    have lmm₁ : 0 < weight μ.val υ, from weight_pos_of υ h₁,
    have lmm₂ : get_inv_up μ.val υ = none, from eq_none_of_out_neq_infinity υ h₂, simp at*,
    simp[lambda', eqn_μ, lmm₁, lmm₂] at eqn_μ',
    exact eq.symm (list.head_eq_of_cons_eq eqn_μ')
  end, λ h,
  begin
    have : ∃ m, m < n ∧ lambda' υ m = μ.val ∧ lambda' υ (m + 1) = ∞ :: μ.val,
    { simp[out_eq_iff] at h, exact lambda'_suffix_eq υ h },
    rcases this with ⟨m, eqn_m, eqn_μ, eqn_μ'⟩,
    by_cases C₁ : 0 < weight (lambda' υ m) υ; simp[lambda', C₁] at eqn_μ',
    { cases C₂ : get_inv_up (lambda' υ m) υ with ν; simp[C₂] at eqn_μ',
      { simp[←eqn_μ], refine ⟨of_weight_pos υ C₁, out_neq_infinity_of_eq_none υ C₂⟩ },
      { exfalso, have := list.head_eq_of_cons_eq eqn_μ', simp* at* } },
    { exfalso, simp[eqn_μ] at eqn_μ', exact eqn_μ' }
  end⟩

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

lemma out_neq_infinity_of_out_infinity {η : Tree 0} {μ : branch (S.lambda η)} {η₀ : Tree 0}
  (h : out μ = sum.inr η₀) : ∃ h : η₀ ⊂ᵢ η, out ⟨η₀, h⟩ = ∞ ∧ S.up η₀ = μ.val :=
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
    by_cases C₁ : ∀ s, (S.lambda (Λ.path s)).rnth n = none,
    { refine ⟨s₀, by refl, λ s eqn_s, _⟩, simp[C₁] },
    have C₁ : ∃ s₁ ν, (S.lambda (Λ.path s₁)).rnth n = some ν,
    { simp at C₁, rcases C₁ with ⟨s₁, C₁⟩, have := option.ne_none_iff_exists'.mp C₁, exact ⟨s₁, this⟩ },
    rcases C₁ with ⟨s₁, ν, C₁⟩,
    cases ν,
    { cases ν,
      
      
        } }

end 
--/
end strategy


