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

structure Tree_path (n : ℕ) :=
(path : ℕ → Tree n)
(ordered : ∀ m, path m <:+ path (m + 1))

def branch.cons' {n} {η : Tree n} {a} (μ : branch η) : branch (a :: η) :=
⟨μ.val, μ.property.trans (η.is_initial_cons _)⟩

instance : has_zero (zero ⊕ infinity) := ⟨sum.inl zero.zero⟩

notation `∞` := sum.inl infinity.infinity

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

lemma rnth_eq_iff_out {n} {η : Tree n} {ν} {m : ℕ} :
  η.rnth m = some ν ↔ ν :: η↾*m <:+ η :=
list.rnth_eq_iff_suffix_cons_initial

lemma rnth_eq_some_out {n} {η : Tree n} {μ : branch η} {m : ℕ} (h : m < η.length) :
  η.rnth m = some (out (⟨η↾*m, list.is_initial_of_lt_length h⟩ : branch η)) :=
rnth_eq_iff_out.mpr (suffix_out_cons ⟨η↾*m, list.is_initial_of_lt_length h⟩)

namespace approx

def up_inv (η : Tree 1) : Π {μ : Tree 0} (υ : branch μ → option (Tree 1)), list (Tree 0)
| []       _ := []
| (_ :: μ) υ := if υ ⟨μ, by simp⟩ = ↑η then μ :: @up_inv μ (λ ν, υ ν.cons') else @up_inv μ (λ ν, υ ν.cons')

lemma up_inv_mem_iff {η : Tree 1} : ∀ {μ : Tree 0} {υ : branch μ → option (Tree 1)} {μ₀ : Tree 0},
  μ₀ ∈ up_inv η υ ↔ ∃ h : μ₀ ⊂ᵢ μ, υ ⟨μ₀, h⟩ = η
| []       μ υ  := by simp[up_inv]
| (x :: μ) υ μ₀ := by {
    have IH := @up_inv_mem_iff μ (λ ν, υ ν.cons') μ₀, 
    simp[up_inv],
    by_cases C : υ ⟨μ, by simp⟩ = ↑η; simp[C],
    { simp[IH],
      split,
      { rintros (rfl | ⟨_, h⟩), { exact ⟨_, C⟩ }, { refine ⟨_, h⟩ } },
      { rintros ⟨i, h⟩, simp[branch.cons'],
        have : μ₀ = μ ∨ μ₀ ⊂ᵢ μ, from list.is_initial_cons_iff.mp i,
        cases this, { exact or.inl this }, { exact or.inr ⟨this, h⟩ } } },
    { simp[IH], split,
      { rintros ⟨i, h⟩, exact ⟨_, h⟩ },
      { rintros ⟨i, h⟩, simp[branch.cons'],
        have : μ₀ = μ ∨ μ₀ ⊂ᵢ μ, from list.is_initial_cons_iff.mp i,
        cases this, { exfalso, rcases this with rfl, exact C h },
        { exact ⟨this, h⟩ } } } }

def weight (η : Tree 1) {μ : Tree 0} (υ : branch μ → option (Tree 1)) : ℕ := (up_inv η υ).length

lemma of_weight_pos {η : Tree 1} {μ : Tree 0}
  (υ : branch μ → option (Tree 1)) (pos : 0 < weight η υ) : ∃ μ₀ : branch μ, υ μ₀ = η :=
by { have := up_inv_mem_iff.mp (list.nth_le_mem _ _ pos), rcases this with ⟨_, h⟩,
     refine ⟨_, h⟩ }

lemma weight_pos_of {η : Tree 1} {μ : Tree 0} (υ : branch μ → option (Tree 1))
  (h : ∃ μ₀ : branch μ, υ μ₀ = η) : 0 < weight η υ :=
by { rcases h with ⟨μ₀, h⟩, have := (@up_inv_mem_iff η μ υ μ₀).mpr ⟨μ₀.property, by simp[h]⟩,
     simp[weight], exact list.length_pos_of_mem this }

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
  (h : @get_inv_up η μ₀ (λ x, υ ⟨x, x.property.trans μ₀.property⟩) = some μ₁),
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

private lemma get_inv_up_eq_none_of_eq_some
  {η : Tree 1} {μ : Tree 0} (υ : branch μ → option (Tree 1)) {μ₀ : branch μ}
  (h : get_inv_up η υ = ↑μ₀) :
  @get_inv_up η μ₀ (λ x, υ ⟨x, x.property.trans μ₀.property⟩) = none :=
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
  (out μ₀ = ∞) ∧ (υ μ₀ = η) ∧ (∀ μ₁, μ₁ < μ₀ → υ μ₁ = η → out μ₁ ≠ ∞) ↔ get_inv_up η υ = ↑μ₀ :=
⟨λ ⟨h₁, h₂, h₃⟩,
  begin
    have : ∃ (μ₁ : branch μ), get_inv_up η υ = some μ₁,
      from option.is_some_iff_exists.mp (is_some_of_out_infinity υ μ₀ h₁ h₂),
    rcases this with ⟨μ₁, h_μ₁⟩,
    have lmm : out μ₁ = ∞ ∧ υ μ₁ = ↑η, from out_infinity_of_eq_some υ h_μ₁,
    suffices : ¬ μ₀ < μ₁,
    { have eqn : μ₁ < μ₀ ∨ μ₁ = μ₀, from branch.le_lt.mp (branch.linear.mpr this),
      cases eqn, { exfalso, exact h₃ _ eqn lmm.2 lmm.1 },
      rw [←eqn], exact h_μ₁ },
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
    refine ⟨this.1, this.2, λ μ₁ h₁ h₂ h₃, _⟩, 
    have eqn : @get_inv_up η μ₀.val (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩) = none,
      from get_inv_up_eq_none_of_eq_some υ h,
    have : (@get_inv_up η μ₀.val (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩)).is_some,
    { have : out μ₁ = out ⟨μ₁.val, h₁⟩,
        from @suffix_out_eq _ _ _ μ₁ ⟨μ₁.val, h₁⟩ rfl (list.suffix_of_is_initial μ₀.property),
      refine is_some_of_out_infinity (λ x, υ ⟨x.val, x.property.trans μ₀.property⟩)
      ⟨μ₁.val, h₁⟩ (by rw[←this, h₃]) (by simp; exact h₂) },
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

def lambda' {μ : Tree 0} (υ : branch μ → option (Tree 1)) : ℕ → Tree 1
| 0       := []
| (n + 1) :=
    if 0 < weight (lambda' n) υ then
      if h : (get_inv_up (lambda' n) υ).is_some then
        sum.inr (option.get h).val :: lambda' n
      else ∞ :: lambda' n
    else lambda' n

def lambda {μ : Tree 0} (υ : branch μ → option (Tree 1)) : Tree 1 := lambda' υ μ.length

lemma lambda'_length {μ : Tree 0} (υ : branch μ → option (Tree 1)) :
  ∀ n, (lambda' υ n).length ≤ n
| 0       := by simp[lambda']
| (n + 1) :=
    begin
      by_cases C₁ : 0 < weight (lambda' υ n) υ; simp[lambda', C₁],
      { cases C₂ : get_inv_up (lambda' υ n) υ; simp[C₂]; refine lambda'_length n },
      exact le_add_right (lambda'_length n)
    end    
  
lemma lambda'_mono {μ : Tree 0} (υ : branch μ → option (Tree 1)) : ∀ {n m : ℕ} (le : n ≤ m),
  lambda' υ n <:+ lambda' υ m :=
begin
  suffices : ∀ n m, lambda' υ n <:+ lambda' υ (n + m),
  { intros n m eqn, have := this n (m - n),
    simp[nat.add_sub_of_le eqn] at this, exact this },
  intros n m, induction m with m IH,
  { refl },
  { simp[←nat.add_one, ←add_assoc, lambda'],
    by_cases C₁ : 0 < weight (lambda' υ (n + m)) υ; simp[C₁],
    { cases C₂ : get_inv_up (lambda' υ (n + m)) υ; simp;
      exact IH.trans (list.suffix_cons _ (lambda' υ (n + m))) },
    exact IH }
end

lemma lambda'_length_mono {μ : Tree 0} (υ : branch μ → option (Tree 1)) {n m : ℕ} (le : n ≤ m) :
  (lambda' υ n).length ≤ (lambda' υ m).length :=
list.length_le_of_infix (list.infix_of_suffix (lambda'_mono υ le))

lemma weight0_of_lambda'_length_lt {μ : Tree 0} {υ : branch μ → option (Tree 1)} : ∀ {n : ℕ}
 (h : (lambda' υ n).length < n), weight (lambda' υ n) υ = 0
| 0       h := by simp at h; contradiction
| (n + 1) h := by { simp[lambda'] at h ⊢,
    by_cases C : 0 < weight (lambda' υ n) υ; simp[C] at h ⊢,
    { exfalso, cases get_inv_up (lambda' υ n) υ; simp at h ⊢;
      { simp[weight0_of_lambda'_length_lt h] at C, contradiction } },
    { simp at C, exact C } }

lemma constant_of_lambda'_length_lt {μ : Tree 0} {υ : branch μ → option (Tree 1)} : ∀ {n m : ℕ} (le : n ≤ m)
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

lemma length_eq_of_pos_weight {μ : Tree 0} {υ : branch μ → option (Tree 1)} {n}
  (h : 0 < weight (lambda' υ n) υ) : (lambda' υ n).length = n :=
begin
  have C : (lambda' υ n).length < n ∨ (lambda' υ n).length = n, from lt_or_eq_of_le (lambda'_length υ n),
  cases C,
  { exfalso,
    have : lambda' υ (n + 1) = lambda' υ n, from constant_of_lambda'_length_lt (by simp) C,
    simp[lambda', h] at this,
    cases C₁ : get_inv_up (lambda' υ n) υ; simp[C₁] at this; contradiction },
    exact C
end

lemma lambda'_suffix_eq {μ : Tree 0} (υ : branch μ → option (Tree 1)) : ∀ {n : ℕ}
  {x} {η : Tree 1} (hη : x :: η <:+ lambda' υ n),
  lambda' υ η.length = η ∧ lambda' υ (η.length + 1) = x :: η
| 0       x η h := by { exfalso, simp[lambda', *] at * }
| (n + 1) x η h :=
    begin
      simp[lambda'] at h,
      by_cases C₁ : 0 < weight (lambda' υ n) υ; simp[C₁] at h,
      { have len : (lambda' υ n).length = n, from length_eq_of_pos_weight C₁,
        cases C₂ : get_inv_up (lambda' υ n) υ with ν; simp[C₂] at h,
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

lemma lambda'_up_inv {μ : Tree 0} {υ : branch μ → option (Tree 1)} {n : ℕ}
  (η₀ : branch (lambda' υ n)) : ∃ μ₀ : branch μ, υ μ₀ = η₀ :=
begin
  have : lambda' υ (list.length ↑η₀) = η₀ ∧ lambda' υ (list.length ↑η₀ + 1) = out η₀ :: η₀.val,
    from lambda'_suffix_eq υ (suffix_out_cons η₀),
  rcases this with ⟨lmm₁, lmm₂⟩,
  simp[lambda', lmm₁] at lmm₂,
  by_cases C : 0 < weight ↑η₀ υ; simp[C] at lmm₂,
  { simp[weight] at C,
    have := up_inv_mem_iff.mp (list.nth_le_mem _ _ C), rcases this with ⟨_, h⟩,
    refine ⟨_, h⟩ },
  { contradiction }
end

lemma out_infinity_of_out_inr {μ : Tree 0} (υ : branch μ → option (Tree 1)) {n : ℕ}
  {η : branch (lambda' υ n)} {μ₀ : Tree 0} (h : out η = sum.inr μ₀) :
  ∃ h : μ₀ ⊂ᵢ μ, out ⟨μ₀, h⟩ = ∞ ∧ υ ⟨μ₀, h⟩ = η :=
begin
  have : lambda' υ (list.length ↑η) = η.val ∧ lambda' υ (list.length ↑η + 1) = sum.inr μ₀ :: η.val,
  { simp[out_eq_iff] at h, refine lambda'_suffix_eq υ h },
  rcases this with ⟨eqn_η, eqn_η'⟩, simp[lambda', eqn_η] at eqn_η',
  by_cases C₁ : 0 < weight ↑η υ; simp[C₁] at eqn_η',
  { cases C₂ : get_inv_up ↑η υ with ν; simp[C₂] at eqn_η',
    { exfalso, have := list.head_eq_of_cons_eq eqn_η', simp* at * },
    { have : ν.val = μ₀,
        from sum.inr.inj (list.head_eq_of_cons_eq eqn_η'),
      rcases this with rfl,
      refine ⟨ν.property, _⟩, simp,
      exact out_infinity_of_eq_some υ C₂ } },
  contradiction
end

lemma lambda'_out_iff
  {μ : Tree 0} (υ : branch μ → option (Tree 1)) {n : ℕ} {η : branch (lambda' υ n)} {μ₀ : branch μ} :
  (out μ₀ = ∞) ∧ (υ μ₀ = η) ∧ (∀ μ₁, μ₁ < μ₀ → υ μ₁ = η → out μ₁ ≠ ∞) ↔ out η = sum.inr μ₀.val :=
begin
  have : lambda' υ (list.length ↑η) = η ∧ lambda' υ (list.length ↑η + 1) = out η :: η.val,
    from lambda'_suffix_eq υ (suffix_out_cons η),
  rcases this with ⟨eqn_η, eqn_η'⟩, simp[lambda', eqn_η] at eqn_η',
  by_cases C₁ : 0 < weight ↑η υ; simp[C₁] at eqn_η'; simp[eqn_η] at*,
  { cases C₂ : get_inv_up η υ with μ₁; simp[C₂] at eqn_η',
    { have eqn₁ : ∞ = out η, from list.head_eq_of_cons_eq eqn_η', simp[←eqn₁], 
      intros h₁ h₂, exfalso,
      have : ∀ μ₀, υ μ₀ = η → ¬out μ₀ = ∞ := out_neq_infinity_of_eq_none υ C₂,
      exact this _ h₂ h₁ },
    { have eqn₁ : sum.inr μ₁.val = out η, from list.head_eq_of_cons_eq eqn_η',
      have := @get_inv_up_iff η μ υ μ₀,
      simp[this, C₂, ←eqn₁, ←subtype.ext_iff], unfold_coes, simp, } },
  { contradiction }
end

lemma lambda'_out_iff_infinity
  {μ : Tree 0} (υ : branch μ → option (Tree 1)) {n : ℕ} {η : branch (lambda' υ n)} :
  (∃ μ₀, υ μ₀ = η) ∧ (∀ μ₀, υ μ₀ = η → out μ₀ ≠ ∞) ↔ out η = ∞ :=
⟨λ ⟨h₁, h₂⟩, begin
    have : lambda' υ (list.length ↑η) = η ∧ lambda' υ (list.length ↑η + 1) = out η :: η.val,
      from lambda'_suffix_eq υ (suffix_out_cons η),
    rcases this with ⟨eqn_η, eqn_η'⟩, simp[lambda', eqn_η] at eqn_η',
    have lmm₁ : 0 < weight η.val υ, from weight_pos_of υ h₁,
    have lmm₂ : get_inv_up η.val υ = none, from eq_none_of_out_neq_infinity υ h₂, simp at*,
    simp[lambda', eqn_η, lmm₁, lmm₂] at eqn_η',
    exact eq.symm (list.head_eq_of_cons_eq eqn_η')
  end, λ h,
  begin
    have : lambda' υ (list.length ↑η) = η ∧ lambda' υ (list.length ↑η + 1) = out η :: η.val,
      from lambda'_suffix_eq υ (suffix_out_cons η),
    rcases this with ⟨eqn_η, eqn_η'⟩, simp[lambda', eqn_η] at eqn_η',
    by_cases C₁ : 0 < weight ↑η υ; simp[lambda', C₁] at eqn_η',
    { cases C₂ : get_inv_up ↑η υ with ν; simp[C₂] at eqn_η',
      { exact ⟨of_weight_pos υ C₁, out_neq_infinity_of_eq_none υ C₂⟩ },
      { exfalso, have := list.head_eq_of_cons_eq eqn_η', simp* at* } },
    { contradiction }
  end⟩

private lemma length_le_of_surj {n m : ℕ} {μ : Tree m} (f : branch μ → option (Tree n)) {η : Tree n}
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
      from finset.card_image_of_injective (branch.branch_univ' η) (option.some_injective (Tree n)),
    simp at eqn₂, simp [eqn₂] at eqn₁, exact eqn₁ },
  exact le_trans eqn₂ eqn₁
end

lemma lambda_eq_of_le {μ : Tree 0} (υ : branch μ → option (Tree 1)) : ∀ {n : ℕ} (h : μ.length ≤ n),
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
  have : ∃ (μ₀ : branch μ), υ μ₀ = ↑(lambda υ), from of_weight_pos υ A,
  rcases this with ⟨μ₀, eqn⟩,
  have : ∀ (η₀ : branch (∞ :: (lambda υ))), ∃ (μ₀ : branch μ), υ μ₀ = ↑η₀,
  { intros η₀,
    have : ∀ (η₀ : branch (lambda υ)), ∃ (μ₀ : branch μ), υ μ₀ = ↑η₀, from @lambda'_up_inv μ υ μ.length,
    have C₁ : η₀.val = lambda υ ∨ η₀.val ⊂ᵢ lambda υ, from list.is_initial_cons_iff.mp η₀.property,
    cases C₁,
    { exact ⟨μ₀, by simp[eqn, ←C₁]⟩ },
    { exact this ⟨η₀, C₁⟩ } },
  have : (lambda υ).length + 1 ≤ μ.length,
  { have := length_le_of_surj υ this, simp at this, exact this },
  exact ((lambda υ).length).not_succ_le_self (le_trans this C)
end

lemma lambda'_eq_lambda'_length {μ : Tree 0} (υ : branch μ → option (Tree 1)) (n : ℕ) :
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

lemma lambda_eq_of_le' {μ : Tree 0} {υ : branch μ → option (Tree 1)} {n : ℕ} (h : (lambda υ).length ≤ n) :
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

lemma lambda_initial_eq {μ : Tree 0} (υ : branch μ → option (Tree 1)) {n : ℕ} :
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

def assign {μ : Tree 0} (υ : branch μ → option (Tree 1)) : Π η : Tree 1, option (Tree 1 × ℕ)
| []               := none
| (∞ :: η)        :=
  if h : (assign η).is_some then S.inf (option.get h) (η, weight η υ) else
  some (η, weight η υ)
| (sum.inr _ :: η) := assign η


def assign_eq {μ : Tree 0} (υ : branch μ → option (Tree 1)) : Tree 1 → option (Tree 1 × ℕ) := λ η, assign S υ (∞ :: η)

def assignment {μ : Tree 0} (υ : branch μ → option (Tree 1)) : option (Tree 1 × ℕ) := assign_eq S υ (lambda υ)

def up {μ : Tree 0} (υ : branch μ → option (Tree 1)) : option (Tree 1) := (assignment S υ).map prod.fst

def requirement {μ : Tree 0} (υ : branch μ → option (Tree 1)) : option R := (assignment S υ).map S.requirement

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

def lambda' (η : Tree 0) : ℕ → Tree 1 := approx.lambda' (S.up' η)
def lambda (η : Tree 0) : Tree 1 := approx.lambda (S.up' η)

lemma lambda'_out_iff
  {μ : Tree 0} {n : ℕ} {η : branch (S.lambda' μ n)} {μ₀ : branch μ} :
  (out μ₀ = ∞) ∧ (S.up μ₀ = η) ∧ (∀ μ₁, μ₁ < μ₀ → S.up μ₁ = η → out μ₁ ≠ ∞) ↔ out η = sum.inr μ₀.val :=
by { have := @approx.lambda'_out_iff μ (S.up' μ) n η μ₀, simp[up'_up_consistent] at this, 
     exact this }

lemma lambda'_out_iff_infinity
  {μ : Tree 0} {n : ℕ} {η : branch (S.lambda' μ n)} :
  (∃ μ₀ : branch μ, S.up μ₀ = η) ∧ (∀ μ₀ : branch μ, S.up μ₀ = η → out μ₀ ≠ ∞) ↔ out η = ∞ :=
by { have := @approx.lambda'_out_iff_infinity μ (S.up' μ) n η, simp[up'_up_consistent] at this, 
     exact this }

def assignment (η : Tree 0) : option (Tree 1 × ℕ) := approx.assignment S (up' S η)
#check up

@[simp] lemma lambda_nil : S.lambda [] = [] := rfl

variables (Λ : Tree_path 0)

lemma lambda_initial_eq {μ : Tree 0} {n : ℕ} :
  (S.lambda μ)↾*n = S.lambda' μ n :=

lemma lambda_defined {μ₁ μ₂ : Tree 0} {n : ℕ} {x}
  (ss : μ₁ ⊆ μ₂) (h : (S.lambda μ₁)↾*n = (S.lambda μ₂)↾*n) (d : (S.lambda μ₁).rnth n = some x) :
  ((S.lambda μ₂).rnth n).is_some :=
begin
  have := list.rnth_some_lt d,
  have := list.initial_length (list.rnth_some_lt d),
end

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
    by_cases C₁ : ∀ s, s₀ ≤ s → (S.lambda (Λ.path s)).rnth n = none,
    { refine ⟨s₀, by refl, λ s eqn_s, _⟩, simp[C₁ s eqn_s, C₁ s₀ (by refl)] },
    have C₁ : ∃ s₁, s₀ ≤ s₁ ∧ ∃ x, (S.lambda (Λ.path s₁)).rnth n = some x,
    { simp at C₁, rcases C₁ with ⟨s₁, eqn, C₁⟩, exact ⟨s₁, eqn, option.ne_none_iff_exists'.mp C₁⟩ },
    rcases C₁ with ⟨s₁, eqn_s₁, ν, C₁⟩,
    by_cases C₂ : ∀ s, s₁ ≤ s → (S.lambda (Λ.path s)).rnth n = some ∞,
    { refine ⟨s₁, eqn_s₁, λ s eqn_s, _⟩, simp[C₂, C₂ s eqn_s] },
    have C₂ : ∃ s₂, s₁ ≤ s₂ ∧ ∃ (ν : Tree 0), (S.lambda (Λ.path s₂)).rnth n = some (sum.inr ν),
    { simp at C₂, rcases C₂ with ⟨s₂, eqn_s₂, C₂⟩,
      refine ⟨s₂, eqn_s₂, _⟩,
      cases C : (S.lambda (Λ.path s₂)).rnth n,
      {  }  }  }

end 


theorem finite_injury' :
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
    rcases C₁ with ⟨s₁, ν, C₁⟩,  }

end 
--/
end strategy


