import lib tree

open encodable denumerable

attribute [simp] set.set_of_app_iff

structure strategy :=
(n : ℕ)
(omega_ordering (k : ℕ) : omega_ordering (Tree k × ℕ))

namespace strategy
variables (S : strategy)

namespace approx
variables {k : ℕ}

def derivative (η : Tree (k + 1)) {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : list (ancestor μ) :=
μ.ancestors.filter (λ a, υ a = η)

lemma derivative_ordered (η : Tree (k + 1)) {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) :
  (derivative η υ).ordered (<) :=
by simp[derivative]; exact list.ordered_filter _ (ancestor.ancestors_ordered μ)

def initial_derivative
  (η : Tree (k + 1)) {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : option (ancestor μ) :=
(derivative η υ).nth 0

def pie_derivative
  (η : Tree (k + 1)) {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : list (ancestor μ) :=
(derivative η υ).filter (λ μ₀, (out μ₀).is_pie)

def principal_derivative
  (η : Tree (k + 1)) {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : option (ancestor μ) :=
((pie_derivative η υ).nth 0).cases_on' (initial_derivative η υ) some

def lambda : ∀ {μ : Tree k} (υ : ancestor μ → Tree (k + 1)), Tree (k + 1)
| []       _ := []
| (x :: μ) υ := let ih := lambda (ancestor.extend_fn υ μ (by simp)) in 
    if υ ⟨μ, by simp⟩ = ih ∨
    (x.is_pie ∧ pie_derivative (υ ⟨μ, by simp⟩) (ancestor.extend_fn υ μ (by simp)) = [])
    then (x :: μ) :: (υ ⟨μ, by simp⟩) else ih

def assignment {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : Tree (k + 1) × ℕ :=
(S.omega_ordering (k + 1)).Min_le
  ((lambda υ, 0) :: ((lambda υ).ancestors.filter (λ η, (out η).is_pie)).map (λ η, (η.val, (derivative η.val υ).length))) (by simp)

def up {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : Tree (k + 1) :=
(assignment S υ).1

end approx
variables {k : ℕ}

def up' : Π (η : Tree k) (μ : ancestor η), Tree (k + 1)
| []       ⟨μ, μ_p⟩ := by exfalso; simp* at*
| (_ :: η) ⟨μ, _⟩   := if h : μ ⊂ᵢ η then up' η ⟨μ, h⟩ else approx.up S (up' η)

def assignment (η : Tree k) : Tree (k + 1) × ℕ := approx.assignment S (up' S η)

def up (η : Tree k) : Tree (k + 1) := approx.up S (up' S η)

@[simp] lemma up'_up_consistent {η : Tree k} : ∀ (μ : ancestor η), S.up' η μ = S.up μ.val :=
begin
  induction η with ν η IH,
  { intros μ, have := μ.property, simp* at* },
  { intros μ, cases μ with μ μ_p, 
    have : μ = η ∨ μ ⊂ᵢ η, from list.is_initial_cons_iff.mp μ_p,
    cases this; simp[this, up'],
    { refl }, { exact IH _ } }
end

lemma up'_up_consistent' {η : Tree k} : S.up' η = λ μ, S.up μ.val :=
funext (λ x, by simp)

def derivative (η : Tree (k + 1)) (μ : Tree k) : list (ancestor μ) := approx.derivative η (S.up' μ)

def pie_derivative (η : Tree (k + 1)) (μ : Tree k) : list (ancestor μ) := approx.pie_derivative η (S.up' μ)

def is_link_free (η : Tree (k + 1)) (μ : Tree k) (μ₀ : ancestor μ) : bool :=
((S.derivative η μ).filter (λ ν, ν ≤ μ₀) = []) || ((S.pie_derivative η μ).filter (λ ν, μ₀ ≤ ν) = [])

def lambda (η : Tree k) : Tree (k + 1) := approx.lambda (S.up' η)

@[simp] lemma up_extend {μ₁ μ₂ : Tree k} {h : μ₂ <:+ μ₁} : ancestor.extend_fn (S.up' μ₁) μ₂ h = S.up' μ₂ :=
by { simp[ancestor.extend_fn], exact eq.symm S.up'_up_consistent' }

@[simp] lemma extend_lambda {μ μ₀ : Tree k} (h : μ₀ <:+ μ) :
  approx.lambda (ancestor.extend_fn (S.up' μ) μ₀ h) = S.lambda μ₀ :=
by {simp[ancestor.extend_fn, lambda], congr, funext x, simp}

lemma assignment_fst_eq_up {μ : Tree k} : (S.assignment μ).1 = S.up μ :=
by simp[assignment, up, approx.up]

lemma up_eq_lambda_or_pie (μ : Tree k) : S.up μ = S.lambda μ ∨ ∃ η : ancestor (S.lambda μ), (out η).is_pie ∧ S.up μ = η :=
by { have : S.assignment μ ∈ _, from omega_ordering.Min_le_mem, simp at this,
     cases this,
     { left, simp[←assignment_fst_eq_up, this], refl },
     { right, rcases this with ⟨η, pie, eqn⟩, refine ⟨η, pie, _⟩, simp[←assignment_fst_eq_up, ←eqn] } }

lemma up_eq_or_lt (μ : Tree k) : S.up μ = S.lambda μ ∨ ∃ lt : S.up μ ⊂ᵢ S.lambda μ, (out ⟨S.up μ, lt⟩).is_pie :=
by { have : S.assignment μ ∈ _, from omega_ordering.Min_le_mem, simp at this,
     cases this,
     { left, simp[←assignment_fst_eq_up, this], refl },
     { right, rcases this with ⟨η, pie, eqn⟩, simp[←assignment_fst_eq_up, ←eqn], exact ⟨η.property, pie⟩ } }

@[simp] lemma lambda_nil_eq : S.lambda ([] : Tree k) = [] :=
by simp[lambda, approx.lambda]

lemma lambda_cons_eq (x) (μ : Tree k) : S.lambda (x :: μ) = (x :: μ) :: S.up μ ∨ S.lambda (x :: μ) = S.lambda μ :=
by { unfold lambda, simp[approx.lambda],
     by_cases C : S.up μ = approx.lambda (S.up' μ) ∨ ↥(x.is_pie) ∧ approx.pie_derivative (S.up μ) (S.up' μ) = [];
     simp[C] }

@[simp] lemma up_nil_eq : S.up ([] : Tree k) = [] :=
by { have := S.up_eq_or_lt ([] : Tree k), simp at this, exact this }

-- Consistency

lemma up_le_lambda (μ : Tree k) : S.up μ <:+ S.lambda μ :=
by { rcases S.up_eq_or_lt μ with (eqn | ⟨lt, eqn⟩), { simp[eqn] }, { exact list.suffix_of_is_initial lt } }

lemma eq_lambda_of_le_lambda {μ : Tree k} {η : Tree (k + 1)} (le : η <:+ S.lambda μ) :
  η = [] ∨ ∃ μ₀ : ancestor μ, η = S.lambda ((out μ₀) :: μ₀.val) ∧ 
  (S.up μ₀.val = S.lambda μ₀.val ∨
    (out μ₀).is_pie ∧ (∀ (a : ancestor μ₀.val), a ∈ S.derivative (S.up μ₀.val) μ₀.val → (out a).is_sigma)) ∧
    η = ((out μ₀) :: μ₀.val) :: S.up μ₀ :=
begin
  induction μ with x μ IH,
  { left, simp[lambda, approx.lambda] at le, exact le },
  { by_cases C :
      S.up μ = S.lambda μ ∨ x.is_pie ∧ approx.pie_derivative (S.up μ) (S.up' μ) = list.nil,
    { have eqn : S.lambda (x :: μ) = (x :: μ) :: S.up μ, { unfold lambda at*, simp[approx.lambda, C] },
      have C₂ : η = (x :: μ) :: S.up μ ∨ η <:+ S.up μ,
      { simp [eqn] at le, exact list.suffix_cons_iff.mp le },
      rcases C₂ with (rfl | C₂),
      { refine or.inr ⟨⟨μ, by simp⟩, _⟩, simp[eqn, C],
        simp[approx.pie_derivative, list.filter_eq_nil] at C, exact C },
      { have := IH (C₂.trans (S.up_le_lambda μ)),
        rcases this with (rfl | ⟨μ₀, rfl, eqn⟩), { simp },
        { refine or.inr ⟨μ₀.extend (by simp), _⟩, simp, exact eqn } } },
    { have eqn : S.lambda (x :: μ) = S.lambda μ,
      { unfold lambda, simp[approx.lambda, C, show approx.lambda (S.up' μ) = S.lambda μ, by refl] },
      have := IH (by { simp[←eqn, le] }),
      rcases this with (rfl | ⟨μ₀, rfl, eqn⟩), { simp },
      refine or.inr ⟨μ₀.extend (by simp), _⟩, simp, exact eqn } }
end

lemma eq_lambda_of_lt_lambda {μ : Tree k} (η : ancestor (S.lambda μ)) :
  ∃ μ₀ : ancestor μ, out η :: η.val = S.lambda ((out μ₀) :: μ₀.val) ∧
  ( S.up μ₀.val = S.lambda μ₀ ∨
    (out μ₀).is_pie ∧ ∀ (ν : ancestor μ₀.val), ν ∈ S.derivative (S.up ↑μ₀) μ₀.val → (out ν).is_sigma ) ∧
  out η = (out μ₀) :: μ₀.val ∧ η.val = S.up μ₀ :=
by { have := S.eq_lambda_of_le_lambda (suffix_out_cons η), simp at this,
     rcases this with ⟨μ₀, eqn₁, h, eqn₂⟩,
     exact ⟨μ₀, eqn₁, h, list.head_eq_of_cons_eq eqn₂, list.tail_eq_of_cons_eq eqn₂⟩ }


lemma suffix_of_mem_lambda {ρ μ : Tree k}
  (h : μ ∈ S.lambda ρ) : μ <:+ ρ :=
begin
  rcases list.mem_iff_rnth.mp h with ⟨n, eqn⟩,
  have le₁ : μ :: S.lambda ρ↾*n <:+ S.lambda ρ, from list.rnth_eq_iff_suffix_cons_initial.mp eqn,
  have lt : S.lambda ρ↾*n ⊂ᵢ S.lambda ρ, from list.suffix_cons_iff_is_initial.mp ⟨_, le₁⟩,
  rcases S.eq_lambda_of_lt_lambda ⟨_, lt⟩ with ⟨μ₀, _, _, out_eq, _⟩,
  have : μ = out μ₀ :: μ₀.val,
  { have := list.suffix_or_suffix_of_suffix le₁ (out_eq_iff.mp out_eq), simp at this,
    cases this; simp [this] },
  simp[this],
  exact suffix_out_cons μ₀
end

lemma suffix_out {ρ : Tree k}
  (η : ancestor (S.lambda ρ)) : out η <:+ ρ :=
S.suffix_of_mem_lambda (by { rcases suffix_out_cons η with ⟨l, eqn⟩, simp[←eqn] })

lemma noninitial_of_suffix {μ₁ μ₂ : Tree k}
  (lt : μ₁ <:+ μ₂) : ¬S.lambda μ₂ ⊂ᵢ S.lambda μ₁ :=
begin
  rcases lt with ⟨l, rfl⟩,
  induction l with x ν IH,
  { simp },
  { by_cases C : S.up (ν ++ μ₁) = approx.lambda (S.up' (ν ++ μ₁)) ∨
      (x.is_pie) ∧ approx.pie_derivative (S.up (ν ++ μ₁)) (S.up' (ν ++ μ₁)) = [],
    { intros h,
      have lambda_eqn : S.lambda (x :: (ν ++ μ₁)) = (x :: (ν ++ μ₁)) :: S.up (ν ++ μ₁),
      { simp[lambda, approx.lambda, C] },
      simp[lambda_eqn] at h,
      have : x :: (ν ++ μ₁) <:+ μ₁, from S.suffix_of_mem_lambda (by { rcases h with ⟨l, a, eqn⟩, simp[←eqn] }),
      have : μ₁ <:+ μ₁ ∧ μ₁ ≠ μ₁, from list.is_initial_iff_suffix.mp
          (by rw [←list.cons_append] at this; exact list.is_initial_of_pos_suffix this (by simp)),
      simp at this, contradiction },
    have lambda_eqn : S.lambda (x :: (ν ++ μ₁)) = S.lambda (ν ++ μ₁),
      { simp[lambda, approx.lambda, C] }, simp[lambda_eqn], exact IH }
end

@[simp] lemma noninitial_of_suffix' {μ ν : Tree k} : ¬S.lambda (ν ++ μ) ⊂ᵢ S.lambda μ :=
S.noninitial_of_suffix (by simp)

lemma incomparable_of_incomparable {μ₁ μ₂ μ₃ : Tree k}
  (le₁ : μ₁ <:+ μ₂) (le₂ : μ₂ <:+ μ₃) (h : S.lambda μ₁ ∥ S.lambda μ₂) : S.lambda μ₁ ∥ S.lambda μ₃ :=
begin
  rcases le₂ with ⟨l, rfl⟩,
  induction l with x ν IH,
  { simp[h] },
  { by_cases C : S.up (ν ++ μ₂) = approx.lambda (S.up' (ν ++ μ₂)) ∨
      (x.is_pie) ∧ approx.pie_derivative (S.up (ν ++ μ₂)) (S.up' (ν ++ μ₂)) = list.nil; simp[C],
    { have lambda_eqn : S.lambda (x :: (ν ++ μ₂)) = (x :: (ν ++ μ₂)) :: S.up (ν ++ μ₂),
      { simp[lambda, approx.lambda, C] },
      refine list.incomparable_iff_suffix_is_initial.mpr ⟨λ A, _, λ A, _⟩,
      { have C₂ : S.lambda μ₁ <:+ S.up (ν ++ μ₂),
        { rw [lambda_eqn] at A, exact list.is_initial_cons_iff_suffix.mp A },
        { have := IH.1 (C₂.trans (S.up_le_lambda (ν ++ μ₂))), contradiction } },
      { rw [lambda_eqn] at A,
        have : x :: (ν ++ μ₂) <:+ μ₁, from S.suffix_of_mem_lambda (by rcases A with ⟨l, eqn⟩; simp[←eqn]),
        have : μ₂ <:+ μ₁ ∧ μ₂ ≠ μ₁, from list.is_initial_iff_suffix.mp
          (by rw [←list.cons_append] at this; exact list.is_initial_of_pos_suffix this (by simp)),
        rcases list.suffix_antisymm le₁ this.1 with rfl, simp at this, contradiction } },
    have lambda_eqn : S.lambda (x :: (ν ++ μ₂)) = S.lambda (ν ++ μ₂),
      { simp[lambda, approx.lambda, C] },
    simp[lambda_eqn], exact IH }
end

lemma suffix_of_suffix {μ₁ μ₂ μ₃ : Tree k}
  (le₁ : μ₁ <:+ μ₂) (le₂ : μ₂ <:+ μ₃) (h : S.lambda μ₁ <:+ S.lambda μ₃) : S.lambda μ₁ <:+ S.lambda μ₂ :=
by { have := mt (S.incomparable_of_incomparable le₁ le₂) (λ nonle, nonle.1 h),
     simp[list.incomparable_iff_is_initial_suffix, S.noninitial_of_suffix le₁] at this, exact this }

lemma sigma_preserve {μ₁ : Tree k} {μ₂ : Tree k} (le : μ₁ <:+ μ₂)
  {η : ancestor (S.lambda μ₁)} (sigma : (out η).is_sigma) (lt : η.val ⊂ᵢ S.lambda μ₂) :
  out η :: η.val <:+ S.lambda μ₂ :=
begin
  rcases le with ⟨l, rfl⟩,
  induction l with x ν IH,
  { simp, exact suffix_out_cons η },
  { by_cases C : S.up (ν ++ μ₁) = approx.lambda (S.up' (ν ++ μ₁)) ∨
      (x.is_pie) ∧ approx.pie_derivative (S.up (ν ++ μ₁)) (S.up' (ν ++ μ₁)) = [],
    { have lambda_eqn : S.lambda (x :: (ν ++ μ₁)) = (x :: (ν ++ μ₁)) :: S.up (ν ++ μ₁),
      { simp[lambda, approx.lambda, C] },
      have le : η.val <:+ S.up (ν ++ μ₁), { simp[lambda_eqn] at lt, exact list.is_initial_cons_iff_suffix.mp lt },      
      have lt : η.val ⊂ᵢ S.lambda (ν ++ μ₁),
      { have := le.trans (S.up_le_lambda _),
        have C₂ := list.suffix_iff_is_initial.mp this, rcases C₂, exact C₂,
        have := η.property, simp[C₂] at this, contradiction },
      have IH' : out η :: η.val <:+ S.lambda (ν ++ μ₁), from IH lt,
      have C₂ : η.val ⊂ᵢ S.up (ν ++ μ₁) ∨ η.val = S.up (ν ++ μ₁), from list.suffix_iff_is_initial.mp le,
      cases C₂,
      { rcases list.suffix_cons_iff_is_initial.mpr C₂ with ⟨y, eqn⟩,
        have : out η = y,
        { have := list.suffix_of_suffix_length_le IH' (eqn.trans (S.up_le_lambda _)) (by simp),
          simp at this, exact this },
        simp[lambda_eqn, this], exact eqn.trans (by simp) },
      { have C₃ := S.up_eq_or_lt (ν ++ μ₁), rcases C₃ with (eqn | ⟨lt_up, pie⟩),
        { exfalso, simp[eqn] at C₂, simp[C₂] at lt, contradiction },
        { exfalso,
          have : out ⟨η.val, lt⟩ = out η, from out_eq_iff.mpr IH',
          have : out ⟨S.up (ν ++ μ₁), lt_up⟩ = out η, rw←this, from suffix_out_eq (by simp[C₂]) (by refl),
          simp[this] at pie, exact neg_is_pie_iff.mpr sigma pie } } },
    { have lambda_eqn : S.lambda (x :: (ν ++ μ₁)) = S.lambda (ν ++ μ₁),
      { simp[lambda, approx.lambda, C] },
      simp[lambda_eqn] at lt ⊢, exact IH lt } }
end

lemma eq_out_of_sigma {μ₁ μ₂ : Tree k} (le : μ₁ <:+ μ₂) {η : Tree (k + 1)}
  (lt₁ : η ⊂ᵢ S.lambda μ₁) (lt₂ : η ⊂ᵢ S.lambda μ₂) (sigma : (out ⟨η, lt₁⟩).is_sigma) :
  out ⟨η, lt₁⟩ = out ⟨η, lt₂⟩ :=
begin
  have lmm₁ : out ⟨η, lt₁⟩ :: η <:+ S.lambda μ₂, from S.sigma_preserve le sigma lt₂,
  have lmm₂ : out ⟨η, lt₂⟩ :: η <:+ S.lambda μ₂, from suffix_out_cons ⟨η, lt₂⟩,
  have := list.suffix_of_suffix_length_le lmm₁ lmm₂ (by simp), simp at this, exact this
end

lemma up_eq_lambda_of_pie {μ : Tree k} {η : ancestor (S.lambda μ)} (pie : (out η).is_pie) :
  ∃ ν : ancestor μ, out η = out ν :: ν.val ∧ S.lambda ν.val = η ∧ S.lambda (out ν :: ν.val) = out η :: η.val :=
begin
  rcases S.eq_lambda_of_lt_lambda η with ⟨ν, eqn_lam, (eqn_up₁ | ⟨pie', _⟩), eqn_out, eqn_up₂⟩,
  { refine ⟨ν, eqn_out, by simp[←eqn_up₁, ←eqn_up₂], _⟩, rw [eqn_lam] },
  { exfalso, simp[eqn_out] at pie, exact not_pie_sigma pie' pie }
end

lemma eq_out_of_pie {μ₁ μ₂ : Tree k} (le : μ₁ <:+ μ₂) {η : Tree (k + 1)}
  (lt₁ : η ⊂ᵢ S.lambda μ₁) (lt₂ : η ⊂ᵢ S.lambda μ₂) (pie : (out ⟨η, lt₂⟩).is_pie) :
  out ⟨η, lt₁⟩ = out ⟨η, lt₂⟩ :=
begin
  have C₁ : (out ⟨η, lt₁⟩).is_pie ∨ (out ⟨η, lt₁⟩).is_sigma, from pie_or_sigma (out ⟨η, lt₁⟩),
  cases C₁,
  { rcases S.up_eq_lambda_of_pie pie with ⟨⟨ν₁, lt_ν₁⟩, eqn_out₁, eqn_lam₁, eqn_lam₁'⟩, simp at eqn_lam₁ eqn_out₁ eqn_lam₁',
    rcases S.up_eq_lambda_of_pie C₁ with ⟨⟨ν₂, lt_ν₂⟩, eqn_out₂, eqn_lam₂, eqn_lam₂'⟩, simp at eqn_lam₂ eqn_out₂ eqn_lam₂',
    have lt_ν₂' : ν₂ ⊂ᵢ μ₂, from list.suffix_of_is_initial_is_initial lt_ν₂ le,
    have eqn_out_out : out ⟨ν₂, lt_ν₂'⟩ = out ⟨ν₂, lt_ν₂⟩, from suffix_out_eq (by simp) le,
    suffices : ν₁ = ν₂,
    { rcases this with rfl, 
      simp[eqn_out₁, eqn_out₂, eqn_out_out] },
    have C : ν₁ ⊂ᵢ ν₂ ∨ ν₁ = ν₂ ∨ ν₂ ⊂ᵢ ν₁,
    { have : ancestor.mk' lt_ν₁ < ancestor.mk' lt_ν₂' ∨
        ancestor.mk' lt_ν₁ = ancestor.mk' lt_ν₂' ∨ ancestor.mk' lt_ν₂' < ancestor.mk' lt_ν₁,
      exact trichotomous (ancestor.mk' lt_ν₁) (ancestor.mk' lt_ν₂'), simp[ancestor.lt_iff] at this,
      exact this },
    cases C,
    { exfalso,
      have : out ⟨ν₁, lt_ν₁⟩ :: ν₁ <:+ ν₂,
      { have eqn : out ⟨ν₁, lt_ν₁⟩ = out ⟨ν₁, C⟩, refine suffix_out_eq (by simp) (list.suffix_of_is_initial lt_ν₂'),
        have := suffix_out_cons ⟨ν₁, C⟩, simp at this, simp[eqn, this] },
      have := S.noninitial_of_suffix this, simp[eqn_lam₁', eqn_lam₂] at this, contradiction }, cases C,
    { exact C },
    { exfalso,
      have : ν₁ ⊂ᵢ μ₁,
      { have := lt_or_le_of_le_of_le (list.suffix_of_is_initial lt_ν₁) le,
        cases this, { exact this }, { exfalso, simp[←eqn_lam₁] at lt₁, exact noninitial_of_suffix S this lt₁ } },
      have : out ⟨ν₂, lt_ν₂⟩ :: ν₂ <:+ ν₁,
      { have eqn : out ⟨ν₂, lt_ν₂⟩ = out ⟨ν₂, C⟩, refine suffix_out_eq (by simp) (list.suffix_of_is_initial this),
        have := suffix_out_cons ⟨ν₂, C⟩, simp at this, simp[eqn, this] },
      have := S.noninitial_of_suffix this, simp[eqn_lam₂', eqn_lam₁] at this, contradiction } },
  { exact S.eq_out_of_sigma le lt₁ lt₂ C₁ }
end

lemma lt_lambda_of_lt_le {μ₁ μ₂ : Tree k} (le : μ₁ <:+ μ₂)
  {η : Tree (k + 1)} (lt : η ⊂ᵢ S.lambda μ₁) (le_η : η <:+ S.lambda μ₂) : η ⊂ᵢ S.lambda μ₂ :=
begin
  have C₁ : η ⊂ᵢ S.lambda μ₂ ∨ η = S.lambda μ₂, from list.suffix_iff_is_initial.mp le_η,
  rcases C₁ with (C₁ | rfl),
  { exact C₁ },
  { exfalso, exact S.noninitial_of_suffix le lt }
end

private lemma sigma_outcome_of_eq_up (μ) {μ₁ μ₂ : Tree k} (lt₁ : μ₁ ⊂ᵢ μ₂) (lt₂ : μ₂ ⊂ᵢ μ)
  (eqn : S.up μ₁ = S.up μ₂) (up_lt : S.up μ₂ ⊂ᵢ S.lambda μ₂) : (out ⟨μ₁, lt₁⟩).is_sigma :=
begin
  suffices : ¬(out ⟨μ₁, lt₁⟩).is_pie,
  { simp[Tree'.is_sigma, this], cases (out ⟨μ₁, lt₁⟩).is_pie; simp at this ⊢, contradiction },
  intros A,
  induction μ with x μ IH generalizing μ₁ μ₂,
  { simp at lt₂, contradiction },
  { have up_lt₁ : S.up μ₁ ⊂ᵢ S.lambda μ₂, { simp[eqn, up_lt] },
    have C₁ : μ₂ ⊂ᵢ μ ∨ μ₂ = μ, from list.suffix_iff_is_initial.mp (list.is_initial_cons_iff_suffix.mp lt₂),
    rcases C₁ with (C₁ | rfl),
    { exact IH lt₁ C₁ eqn up_lt A },
    { have eqn_lam₁ : S.lambda (out ⟨μ₁, lt₁⟩ :: μ₁) = (out ⟨μ₁, lt₁⟩ :: μ₁) :: S.up μ₁,
      { have C₂ : S.up μ₁ ⊂ᵢ S.lambda μ₁ ∨ S.up μ₁ = S.lambda μ₁, from list.suffix_iff_is_initial.mp (S.up_le_lambda μ₁),
        cases C₂,
        { have : approx.pie_derivative (S.up μ₁) (S.up' μ₁) = [],
          { simp[approx.pie_derivative, approx.derivative, list.filter_eq_nil],
            rintros ⟨ν, lt_ν⟩ pie_ν eqn_ν, exact IH lt_ν lt₁ eqn_ν C₂ pie_ν },
          unfold lambda, simp[approx.lambda, A, this] },
        { unfold lambda at C₂ ⊢, simp[approx.lambda, C₂] } },
      have out_eq : out (⟨S.up μ₁, by simp[eqn_lam₁]⟩ : ancestor (S.lambda (out ⟨μ₁, lt₁⟩ :: μ₁))) = out ⟨μ₁, lt₁⟩ :: μ₁,
        from out_eq_iff.mpr (by simp[eqn_lam₁]),      
      have : out ⟨S.up μ₁, _⟩ = out ⟨S.up μ₁, up_lt₁⟩,
        from @eq_out_of_sigma S _ (out ⟨μ₁, lt₁⟩ :: μ₁) μ₂ (suffix_out_cons ⟨μ₁, lt₁⟩)
        (S.up μ₁) (by simp[eqn_lam₁]) up_lt₁ (by simp[out_eq, Tree'.is_sigma, A]),
      have sigma : (out ⟨S.up μ₁, up_lt₁⟩).is_sigma,
      { simp[←this, out_eq, Tree'.is_sigma, A] },
      have C₂ := S.up_eq_or_lt μ₂, rcases C₂ with (eqn | ⟨lt', pie⟩),
      { simp[eqn] at up_lt, contradiction },
      { simp[←eqn] at pie lt', exact neg_is_pie_iff.mpr sigma pie } } }
end

lemma sigma_outcome_of_eq_up {μ₁ μ₂ : Tree k} (lt : μ₁ ⊂ᵢ μ₂)
  (eqn : S.up μ₁ = S.up μ₂) (up_lt : S.up μ₂ ⊂ᵢ S.lambda μ₂) : (out ⟨μ₁, lt⟩).is_sigma :=
sigma_outcome_of_eq_up S ((default _) :: μ₂) lt (by simp) eqn up_lt

variables (Λ : Path k)

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
    { have : ∃ s₁, s₀ ≤ s₁ ∧ ∃ x, (S.lambda (Λ.path s₁)).rnth n = some x,
      { simp at C₁, rcases C₁ with ⟨s₁, eqn, C₁⟩, exact ⟨s₁, eqn, option.ne_none_iff_exists'.mp C₁⟩ },
      rcases this with ⟨s₁, eqn_s₁, ν, C₁⟩,
      have IH' : ∀ (s : ℕ), s₁ ≤ s → S.lambda (Λ.path s)↾*n = S.lambda (Λ.path s₁)↾*n, 
      { intros s le, simp[IH s₁ eqn_s₁, IH s (eqn_s₁.trans le)] },
      have lt : S.lambda (Λ.path s₁)↾*n ⊂ᵢ S.lambda (Λ.path s₁),
        from list.suffix_cons_iff_is_initial.mp ⟨_, list.rnth_eq_iff_suffix_cons_initial.mp C₁⟩,
      have lt' : ∀ s, s₁ ≤ s → S.lambda (Λ.path s₁)↾*n ⊂ᵢ S.lambda (Λ.path s),
      { intros s eqn_s, refine S.lt_lambda_of_lt_le (Λ.mono' eqn_s) lt
        (by { simp[←IH' s eqn_s], exact list.suffix_initial _ _}) },
      have rnth_eqn : ∀ s (le : s₁ ≤ s), (S.lambda (Λ.path s)).rnth n = some (out ⟨S.lambda (Λ.path s₁)↾*n, lt' s le⟩),
      { intros s le, refine list.rnth_eq_iff_suffix_cons_initial.mpr _, have := suffix_out_cons ⟨_, lt' s le⟩,
        simp[IH' s le], exact this },
      by_cases C₂ : ∀ (s : ℕ) (le : s₁ ≤ s), (out ⟨S.lambda (Λ.path s₁)↾*n, lt' s le⟩).is_pie,
      { refine ⟨s₁, eqn_s₁, λ s eqn_s, _⟩, simp[rnth_eqn, rnth_eqn _ eqn_s],
        refine eq.symm (S.eq_out_of_pie (Λ.mono' eqn_s) _ _ (by simp[C₂])) },
      { have : ∃ s₂ (h : s₁ ≤ s₂), ↥((out ⟨S.lambda (Λ.path s₁)↾*n, lt' s₂ h⟩).is_sigma),
        { simp at C₂, exact C₂ },
        rcases this with ⟨s₂, eqn_s₂, C₂⟩,
        refine ⟨s₂, eqn_s₁.trans eqn_s₂, λ s eqn_s, _⟩, simp[rnth_eqn _ eqn_s₂, rnth_eqn _ (eqn_s₂.trans eqn_s)], 
        refine eq.symm (S.eq_out_of_sigma (Λ.mono' eqn_s) _ _ C₂) } } }
end

end strategy


