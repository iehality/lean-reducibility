import lib tree reducibility

open encodable denumerable

attribute [simp] set.set_of_app_iff

structure strategy (n : ℕ) :=
(priority (k : ℕ) : omega_ordering (Tree k × ℕ))

namespace strategy

protected def default (n : ℕ) : strategy n := ⟨λ k, omega_ordering.default _⟩

instance (n) : inhabited (strategy n) := ⟨strategy.default n⟩

variables {n₀ : ℕ} (S : strategy n₀)

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

def pi_derivative
  (η : Tree (k + 1)) {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : list (ancestor μ) :=
(derivative η υ).filter (λ μ₀, (out μ₀).is_pi)

def principal_derivative
  (η : Tree (k + 1)) {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : option (ancestor μ) :=
((pi_derivative η υ).nth 0).cases_on' (initial_derivative η υ) some

def lambda : ∀ {μ : Tree k} (υ : ancestor μ → Tree (k + 1)), Tree (k + 1)
| []       _ := []
| (x :: μ) υ := let ih := lambda (ancestor.extend_fn υ μ (by simp)) in 
    if υ ⟨μ, by simp⟩ = ih ∨
    (x.is_pi ∧ pi_derivative (υ ⟨μ, by simp⟩) (ancestor.extend_fn υ μ (by simp)) = [])
    then (x :: μ) :: (υ ⟨μ, by simp⟩) else ih

def assignment {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : Tree (k + 1) × ℕ :=
(S.priority (k + 1)).Min_le
  ((lambda υ, 0) :: ((lambda υ).ancestors.filter (λ η, (out η).is_pi)).map (λ η, (η.val, (derivative η.val υ).length))) (by simp)

def up {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) : Tree (k + 1) :=
(assignment S υ).1

end approx
variables {k : ℕ}

def up' : Π (η : Tree k) (μ : ancestor η), Tree (k + 1)
| []       ⟨μ, μ_p⟩ := by exfalso; simp* at*
| (_ :: η) ⟨μ, _⟩   := if h : μ ⊂ᵢ η then up' η ⟨μ, h⟩ else approx.up S (up' η)

def assignment (η : Tree k) : Tree (k + 1) × ℕ := approx.assignment S (up' S η)

def up (η : Tree k) : Tree (k + 1) := approx.up S (up' S η)

notation `up[` S `]` := up S

@[simp] lemma up'_up_consistent {η : Tree k} : ∀ (μ : ancestor η), S.up' η μ = up[S] μ.val :=
begin
  induction η with ν η IH,
  { intros μ, have := μ.property, simp* at* },
  { intros μ, cases μ with μ μ_p, 
    have : μ = η ∨ μ ⊂ᵢ η, from list.is_initial_cons_iff.mp μ_p,
    cases this; simp[this, up'],
    { refl }, { exact IH _ } }
end

lemma up'_up_consistent' {η : Tree k} : S.up' η = λ μ, up[S] μ.val :=
funext (λ x, by simp)

def derivative (η : Tree (k + 1)) (μ : Tree k) : list (ancestor μ) := approx.derivative η (S.up' μ)

lemma derivative_cons (η : Tree (k + 1)) (ν) (μ : Tree k) :
  S.derivative η (ν :: μ) = if up[S] μ = η then ⟨μ, by simp⟩ :: (S.derivative η μ).map (ancestor.extend (by simp)) else 
    (S.derivative η μ).map (ancestor.extend (by simp)) :=
by { simp[derivative, approx.derivative, list.filter, list.map_filter, function.comp], congr }

def pi_derivative (η : Tree (k + 1)) (μ : Tree k) : list (ancestor μ) := approx.pi_derivative η (S.up' μ)

def is_link_free (η : Tree (k + 1)) (μ : Tree k) (μ₀ : ancestor μ) : bool :=
((S.derivative η μ).filter (λ ν, ν ≤ μ₀) = []) || ((S.pi_derivative η μ).filter (λ ν, μ₀ ≤ ν) = [])

def lambda (η : Tree k) : Tree (k + 1) := approx.lambda (S.up' η)

notation `λ[` S `]` := lambda S


@[simp] lemma up_extend {μ₁ μ₂ : Tree k} {h : μ₂ <:+ μ₁} : ancestor.extend_fn (S.up' μ₁) μ₂ h = S.up' μ₂ :=
by { simp[ancestor.extend_fn], exact eq.symm S.up'_up_consistent' }

@[simp] lemma extend_lambda {μ μ₀ : Tree k} (h : μ₀ <:+ μ) :
  approx.lambda (ancestor.extend_fn (S.up' μ) μ₀ h) = λ[S] μ₀ :=
by { simp[ancestor.extend_fn, lambda], congr, funext x, simp}

lemma assignment_fst_eq_up (μ : Tree k) : (S.assignment μ).1 = up[S] μ :=
by simp[assignment, up, approx.up]

lemma up_eq_lambda_or_pi (μ : Tree k) : up[S] μ = λ[S] μ ∨ ∃ η : ancestor (λ[S] μ), (out η).is_pi ∧ up[S] μ = η :=
by { have : S.assignment μ ∈ _, from omega_ordering.Min_le_mem _ _, simp at this,
     cases this,
     { left, simp[←assignment_fst_eq_up, this], refl },
     { right, rcases this with ⟨η, pi, eqn⟩, refine ⟨η, pi, _⟩, simp[←assignment_fst_eq_up, ←eqn] } }

lemma up_eq_or_lt (μ : Tree k) : up[S] μ = λ[S] μ ∨ ∃ lt : up[S] μ ⊂ᵢ λ[S] μ, (out ⟨up[S] μ, lt⟩).is_pi :=
by { have : S.assignment μ ∈ _, from omega_ordering.Min_le_mem _ _, simp at this,
     cases this,
     { left, simp[←assignment_fst_eq_up, this], refl },
     { right, rcases this with ⟨η, pi, eqn⟩, simp[←assignment_fst_eq_up, ←eqn], exact ⟨η.property, pi⟩ } }

@[simp] lemma lambda_nil_eq : λ[S] ([] : Tree k) = [] :=
by simp[lambda, approx.lambda]

lemma lambda_cons_eq (x) (μ : Tree k) : λ[S] (x :: μ) = (x :: μ) :: up[S] μ ∨ λ[S] (x :: μ) = λ[S] μ :=
by { unfold lambda, simp[approx.lambda],
     by_cases C : up[S] μ = approx.lambda (S.up' μ) ∨ ↥(x.is_pi) ∧ approx.pi_derivative (up[S] μ) (S.up' μ) = [];
     simp[C] }

@[simp] lemma up_nil_eq : up[S] ([] : Tree k) = [] :=
by { have := S.up_eq_or_lt ([] : Tree k), simp at this, exact this }

-- Consistency 1

lemma up_le_lambda (μ : Tree k) : up[S] μ <:+ λ[S] μ :=
by { rcases S.up_eq_or_lt μ with (eqn | ⟨lt, eqn⟩), { simp[eqn] }, { exact list.suffix_of_is_initial lt } }

lemma eq_lambda_of_le_lambda {μ : Tree k} {η : Tree (k + 1)} (le : η <:+ λ[S] μ) :
  η = [] ∨ ∃ μ₀ : ancestor μ, η = λ[S] ((out μ₀) :: μ₀.val) ∧ 
  (up[S] μ₀.val = λ[S] μ₀.val ∨
    (out μ₀).is_pi ∧ (∀ (a : ancestor μ₀.val), a ∈ S.derivative (up[S] μ₀.val) μ₀.val → (out a).is_sigma)) ∧
    η = ((out μ₀) :: μ₀.val) :: up[S] μ₀ :=
begin
  induction μ with x μ IH,
  { left, simp[lambda, approx.lambda] at le, exact le },
  { by_cases C :
      up[S] μ = λ[S] μ ∨ x.is_pi ∧ approx.pi_derivative (up[S] μ) (S.up' μ) = list.nil,
    { have eqn : λ[S] (x :: μ) = (x :: μ) :: up[S] μ, { unfold lambda at*, simp[approx.lambda, C] },
      have C₂ : η = (x :: μ) :: up[S] μ ∨ η <:+ up[S] μ,
      { simp [eqn] at le, exact list.suffix_cons_iff.mp le },
      rcases C₂ with (rfl | C₂),
      { refine or.inr ⟨⟨μ, by simp⟩, _⟩, simp[eqn, C],
        simp[approx.pi_derivative, list.filter_eq_nil] at C, exact C },
      { have := IH (C₂.trans (S.up_le_lambda μ)),
        rcases this with (rfl | ⟨μ₀, rfl, eqn⟩), { simp },
        { refine or.inr ⟨μ₀.extend (by simp), _⟩, simp, exact eqn } } },
    { have eqn : λ[S] (x :: μ) = λ[S] μ,
      { unfold lambda, simp[approx.lambda, C, show approx.lambda (S.up' μ) = λ[S] μ, by refl] },
      have := IH (by { simp[←eqn, le] }),
      rcases this with (rfl | ⟨μ₀, rfl, eqn⟩), { simp },
      refine or.inr ⟨μ₀.extend (by simp), _⟩, simp, exact eqn } }
end

lemma eq_lambda_of_lt_lambda {μ : Tree k} (η : ancestor (λ[S] μ)) :
  ∃ μ₀ : ancestor μ, out η :: η.val = λ[S] ((out μ₀) :: μ₀.val) ∧
  ( up[S] μ₀.val = λ[S] μ₀ ∨
    (out μ₀).is_pi ∧ ∀ (ν : ancestor μ₀.val), ν ∈ S.derivative (up[S] ↑μ₀) μ₀.val → (out ν).is_sigma ) ∧
  out η = (out μ₀) :: μ₀.val ∧ η.val = up[S] μ₀ :=
by { have := S.eq_lambda_of_le_lambda (suffix_out_cons η), simp at this,
     rcases this with ⟨μ₀, eqn₁, h, eqn₂⟩,
     exact ⟨μ₀, eqn₁, h, list.head_eq_of_cons_eq eqn₂, list.tail_eq_of_cons_eq eqn₂⟩ }

lemma eq_lambda_of_le_lambda' {μ : Tree k} {η : Tree (k + 1)} (le : η <:+ λ[S] μ) :
∃ μ₀ : Tree k, μ₀ <:+ μ ∧ η = λ[S] μ₀ :=
begin
  rcases S.eq_lambda_of_le_lambda le with (rfl | ⟨μ₀, eqn₁, _, eqn₂⟩),
  { refine ⟨[], by simp[lambda, approx.lambda, list.nil_suffix]⟩ },
  { refine ⟨out μ₀ :: μ₀.val, by simp[eqn₂]; exact suffix_out_cons _, eqn₁⟩ }
end

lemma eq_lambda_of_pred {μ ν : Tree k} {η : Tree (k + 1)} (eqn : λ[S] μ = ν :: η) : λ[S] ν = λ[S] μ :=
begin
  have lt : η ⊂ᵢ λ[S] μ, { simp[eqn] },
  rcases S.eq_lambda_of_lt_lambda ⟨η, lt⟩ with ⟨μ₀, eqn_lam, _, eqn_out, eqn_up⟩, simp at*,
  have : out ⟨η, lt⟩ = ν, { simp[out_eq_iff, eqn] },
  simp[←eqn_out, this] at eqn_lam, simp[eqn, eqn_lam]
end

lemma initial_of_mem_lambda {ρ μ : Tree k}
  (h : μ ∈ λ[S] ρ) : ∃ μ₀ : ancestor ρ, μ = out μ₀ :: μ₀.val :=
begin
  rcases list.mem_iff_rnth.mp h with ⟨n, eqn⟩,
  have le₁ : μ :: λ[S] ρ↾*n <:+ λ[S] ρ, from list.rnth_eq_iff_suffix_cons_initial.mp eqn,
  have lt : λ[S] ρ↾*n ⊂ᵢ λ[S] ρ, from list.suffix_cons_iff_is_initial.mp ⟨_, le₁⟩,
  rcases S.eq_lambda_of_lt_lambda ⟨_, lt⟩ with ⟨μ₀, _, _, out_eq, _⟩,
  have : μ = out μ₀ :: μ₀.val,
  { have := list.suffix_or_suffix_of_suffix le₁ (out_eq_iff.mp out_eq), simp at this,
    cases this; simp [this] },
  exact ⟨μ₀, this⟩
end

lemma suffix_of_mem_lambda {ρ μ : Tree k}
  (h : μ ∈ λ[S] ρ) : μ <:+ ρ :=
by rcases S.initial_of_mem_lambda h with ⟨μ₀, rfl⟩; exact suffix_out_cons μ₀

lemma out_eq_out {ρ : Tree k}
  (η : ancestor (λ[S] ρ)) : ∃ μ₀ : ancestor ρ, out η = out μ₀ :: μ₀.val :=
S.initial_of_mem_lambda (by { rcases suffix_out_cons η with ⟨l, eqn⟩, simp[←eqn] })

lemma suffix_out {ρ : Tree k}
  (η : ancestor (λ[S] ρ)) : out η <:+ ρ :=
S.suffix_of_mem_lambda (by { rcases suffix_out_cons η with ⟨l, eqn⟩, simp[←eqn] })

lemma noninitial_of_suffix {μ₁ μ₂ : Tree k}
  (lt : μ₁ <:+ μ₂) : ¬λ[S] μ₂ ⊂ᵢ λ[S] μ₁ :=
begin
  rcases lt with ⟨l, rfl⟩,
  induction l with x ν IH,
  { simp },
  { by_cases C : up[S] (ν ++ μ₁) = approx.lambda (S.up' (ν ++ μ₁)) ∨
      (x.is_pi) ∧ approx.pi_derivative (up[S] (ν ++ μ₁)) (S.up' (ν ++ μ₁)) = [],
    { intros h,
      have lambda_eqn : λ[S] (x :: (ν ++ μ₁)) = (x :: (ν ++ μ₁)) :: up[S] (ν ++ μ₁),
      { simp[lambda, approx.lambda, C] },
      simp[lambda_eqn] at h,
      have : x :: (ν ++ μ₁) <:+ μ₁, from S.suffix_of_mem_lambda (by { rcases h with ⟨l, a, eqn⟩, simp[←eqn] }),
      have : μ₁ <:+ μ₁ ∧ μ₁ ≠ μ₁, from list.is_initial_iff_suffix.mp
          (by rw [←list.cons_append] at this; exact list.is_initial_of_pos_suffix this (by simp)),
      simp at this, contradiction },
    have lambda_eqn : λ[S] (x :: (ν ++ μ₁)) = λ[S] (ν ++ μ₁),
      { simp[lambda, approx.lambda, C] }, simp[lambda_eqn], exact IH }
end

@[simp] lemma noninitial_of_suffix' (μ ν : Tree k) : ¬λ[S] (ν ++ μ) ⊂ᵢ λ[S] μ :=
S.noninitial_of_suffix (by simp)

lemma incomparable_of_incomparable {μ₁ μ₂ μ₃ : Tree k}
  (le₁ : μ₁ <:+ μ₂) (le₂ : μ₂ <:+ μ₃) (h : λ[S] μ₁ ∥ λ[S] μ₂) : λ[S] μ₁ ∥ λ[S] μ₃ :=
begin
  rcases le₂ with ⟨l, rfl⟩,
  induction l with x ν IH,
  { simp[h] },
  { by_cases C : up[S] (ν ++ μ₂) = approx.lambda (S.up' (ν ++ μ₂)) ∨
      (x.is_pi) ∧ approx.pi_derivative (up[S] (ν ++ μ₂)) (S.up' (ν ++ μ₂)) = list.nil; simp[C],
    { have lambda_eqn : λ[S] (x :: (ν ++ μ₂)) = (x :: (ν ++ μ₂)) :: up[S] (ν ++ μ₂),
      { simp[lambda, approx.lambda, C] },
      refine list.incomparable_iff_suffix_is_initial.mpr ⟨λ A, _, λ A, _⟩,
      { have C₂ : λ[S] μ₁ <:+ up[S] (ν ++ μ₂),
        { rw [lambda_eqn] at A, exact list.is_initial_cons_iff_suffix.mp A },
        { have := IH.1 (C₂.trans (S.up_le_lambda (ν ++ μ₂))), contradiction } },
      { rw [lambda_eqn] at A,
        have : x :: (ν ++ μ₂) <:+ μ₁, from S.suffix_of_mem_lambda (by rcases A with ⟨l, eqn⟩; simp[←eqn]),
        have : μ₂ <:+ μ₁ ∧ μ₂ ≠ μ₁, from list.is_initial_iff_suffix.mp
          (by rw [←list.cons_append] at this; exact list.is_initial_of_pos_suffix this (by simp)),
        rcases list.suffix_antisymm le₁ this.1 with rfl, simp at this, contradiction } },
    have lambda_eqn : λ[S] (x :: (ν ++ μ₂)) = λ[S] (ν ++ μ₂),
      { simp[lambda, approx.lambda, C] },
    simp[lambda_eqn], exact IH }
end

lemma suffix_of_suffix {μ₁ μ₂ μ₃ : Tree k}
  (le₁ : μ₁ <:+ μ₂) (le₂ : μ₂ <:+ μ₃) (h : λ[S] μ₁ <:+ λ[S] μ₃) : λ[S] μ₁ <:+ λ[S] μ₂ :=
by { have := mt (S.incomparable_of_incomparable le₁ le₂) (λ nonle, nonle.1 h),
     simp[list.incomparable_iff_is_initial_suffix, S.noninitial_of_suffix le₁] at this, exact this }

lemma sigma_preserve {μ₁ : Tree k} {μ₂ : Tree k} (le : μ₁ <:+ μ₂)
  {η : ancestor (λ[S] μ₁)} (sigma : (out η).is_sigma) (lt : η.val ⊂ᵢ λ[S] μ₂) :
  out η :: η.val <:+ λ[S] μ₂ :=
begin
  rcases le with ⟨l, rfl⟩,
  induction l with x ν IH,
  { simp, exact suffix_out_cons η },
  { by_cases C : up[S] (ν ++ μ₁) = approx.lambda (S.up' (ν ++ μ₁)) ∨
      (x.is_pi) ∧ approx.pi_derivative (up[S] (ν ++ μ₁)) (S.up' (ν ++ μ₁)) = [],
    { have lambda_eqn : λ[S] (x :: (ν ++ μ₁)) = (x :: (ν ++ μ₁)) :: up[S] (ν ++ μ₁),
      { simp[lambda, approx.lambda, C] },
      have le : η.val <:+ up[S] (ν ++ μ₁), { simp[lambda_eqn] at lt, exact list.is_initial_cons_iff_suffix.mp lt },      
      have lt : η.val ⊂ᵢ λ[S] (ν ++ μ₁),
      { have := le.trans (S.up_le_lambda _),
        have C₂ := list.suffix_iff_is_initial.mp this, rcases C₂, exact C₂,
        have := η.property, simp[C₂] at this, contradiction },
      have IH' : out η :: η.val <:+ λ[S] (ν ++ μ₁), from IH lt,
      have C₂ : η.val ⊂ᵢ up[S] (ν ++ μ₁) ∨ η.val = up[S] (ν ++ μ₁), from list.suffix_iff_is_initial.mp le,
      cases C₂,
      { rcases list.suffix_cons_iff_is_initial.mpr C₂ with ⟨y, eqn⟩,
        have : out η = y,
        { have := list.suffix_of_suffix_length_le IH' (eqn.trans (S.up_le_lambda _)) (by simp),
          simp at this, exact this },
        simp[lambda_eqn, this], exact eqn.trans (by simp) },
      { have C₃ := S.up_eq_or_lt (ν ++ μ₁), rcases C₃ with (eqn | ⟨lt_up, pi⟩),
        { exfalso, simp[eqn] at C₂, simp[C₂] at lt, contradiction },
        { exfalso,
          have : out ⟨η.val, lt⟩ = out η, from out_eq_iff.mpr IH',
          have : out ⟨up[S] (ν ++ μ₁), lt_up⟩ = out η, rw←this, from suffix_out_eq (by simp[C₂]) (by refl),
          simp[this] at pi, exact neg_is_pi_iff.mpr sigma pi } } },
    { have lambda_eqn : λ[S] (x :: (ν ++ μ₁)) = λ[S] (ν ++ μ₁),
      { simp[lambda, approx.lambda, C] },
      simp[lambda_eqn] at lt ⊢, exact IH lt } }
end

lemma eq_out_of_sigma {μ₁ μ₂ : Tree k} (le : μ₁ <:+ μ₂) {η : Tree (k + 1)}
  (lt₁ : η ⊂ᵢ λ[S] μ₁) (lt₂ : η ⊂ᵢ λ[S] μ₂) (sigma : (out ⟨η, lt₁⟩).is_sigma) :
  out ⟨η, lt₁⟩ = out ⟨η, lt₂⟩ :=
begin
  have lmm₁ : out ⟨η, lt₁⟩ :: η <:+ λ[S] μ₂, from S.sigma_preserve le sigma lt₂,
  have lmm₂ : out ⟨η, lt₂⟩ :: η <:+ λ[S] μ₂, from suffix_out_cons ⟨η, lt₂⟩,
  have := list.suffix_of_suffix_length_le lmm₁ lmm₂ (by simp), simp at this, exact this
end

lemma up_eq_lambda_of_pi {μ : Tree k} {η : ancestor (λ[S] μ)} (pi : (out η).is_pi) :
  ∃ ν : ancestor μ, out η = out ν :: ν.val ∧ λ[S] ν.val = η ∧ λ[S] (out ν :: ν.val) = out η :: η.val :=
begin
  rcases S.eq_lambda_of_lt_lambda η with ⟨ν, eqn_lam, (eqn_up₁ | ⟨pi', _⟩), eqn_out, eqn_up₂⟩,
  { refine ⟨ν, eqn_out, by simp[←eqn_up₁, ←eqn_up₂], _⟩, rw [eqn_lam] },
  { exfalso, simp[eqn_out] at pi, exact not_pi_sigma pi' pi }
end

lemma eq_out_of_pi {μ₁ μ₂ : Tree k} (le : μ₁ <:+ μ₂) {η : Tree (k + 1)}
  (lt₁ : η ⊂ᵢ λ[S] μ₁) (lt₂ : η ⊂ᵢ λ[S] μ₂) (pi : (out ⟨η, lt₂⟩).is_pi) :
  out ⟨η, lt₁⟩ = out ⟨η, lt₂⟩ :=
begin
  have C₁ : (out ⟨η, lt₁⟩).is_pi ∨ (out ⟨η, lt₁⟩).is_sigma, from pi_or_sigma (out ⟨η, lt₁⟩),
  cases C₁,
  { rcases S.up_eq_lambda_of_pi pi with ⟨⟨ν₁, lt_ν₁⟩, eqn_out₁, eqn_lam₁, eqn_lam₁'⟩, simp at eqn_lam₁ eqn_out₁ eqn_lam₁',
    rcases S.up_eq_lambda_of_pi C₁ with ⟨⟨ν₂, lt_ν₂⟩, eqn_out₂, eqn_lam₂, eqn_lam₂'⟩, simp at eqn_lam₂ eqn_out₂ eqn_lam₂',
    have lt_ν₂' : ν₂ ⊂ᵢ μ₂, from list.is_initial.is_initial_of_suffix lt_ν₂ le,
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
  {η : Tree (k + 1)} (lt : η ⊂ᵢ λ[S] μ₁) (le_η : η <:+ λ[S] μ₂) : η ⊂ᵢ λ[S] μ₂ :=
begin
  have C₁ : η ⊂ᵢ λ[S] μ₂ ∨ η = λ[S] μ₂, from list.suffix_iff_is_initial.mp le_η,
  rcases C₁ with (C₁ | rfl),
  { exact C₁ },
  { exfalso, exact S.noninitial_of_suffix le lt }
end

private lemma sigma_outcome_of_eq_up (μ) {μ₁ μ₂ : Tree k} (lt₁ : μ₁ ⊂ᵢ μ₂) (lt₂ : μ₂ ⊂ᵢ μ)
  (eqn : up[S] μ₁ = up[S] μ₂) (up_lt : up[S] μ₂ ⊂ᵢ λ[S] μ₂) : (out ⟨μ₁, lt₁⟩).is_sigma :=
begin
  suffices : ¬(out ⟨μ₁, lt₁⟩).is_pi,
  { simp[Tree'.is_sigma, this] },
  intros A,
  induction μ with x μ IH generalizing μ₁ μ₂,
  { simp at lt₂, contradiction },
  { have up_lt₁ : up[S] μ₁ ⊂ᵢ λ[S] μ₂, { simp[eqn, up_lt] },
    have C₁ : μ₂ ⊂ᵢ μ ∨ μ₂ = μ, from list.suffix_iff_is_initial.mp (list.is_initial_cons_iff_suffix.mp lt₂),
    rcases C₁ with (C₁ | rfl),
    { exact IH lt₁ C₁ eqn up_lt A },
    { have eqn_lam₁ : λ[S] (out ⟨μ₁, lt₁⟩ :: μ₁) = (out ⟨μ₁, lt₁⟩ :: μ₁) :: up[S] μ₁,
      { have C₂ : up[S] μ₁ ⊂ᵢ λ[S] μ₁ ∨ up[S] μ₁ = λ[S] μ₁, from list.suffix_iff_is_initial.mp (S.up_le_lambda μ₁),
        cases C₂,
        { have : approx.pi_derivative (up[S] μ₁) (S.up' μ₁) = [],
          { simp[approx.pi_derivative, approx.derivative, list.filter_eq_nil],
            rintros ⟨ν, lt_ν⟩ pi_ν eqn_ν, exact IH lt_ν lt₁ eqn_ν C₂ pi_ν },
          unfold lambda, simp[approx.lambda, A, this] },
        { unfold lambda at C₂ ⊢, simp[approx.lambda, C₂] } },
      have out_eq : out (⟨up[S] μ₁, by simp[eqn_lam₁]⟩ : ancestor (λ[S] (out ⟨μ₁, lt₁⟩ :: μ₁))) = out ⟨μ₁, lt₁⟩ :: μ₁,
        from out_eq_iff.mpr (by simp[eqn_lam₁]),      
      have : out ⟨up[S] μ₁, _⟩ = out ⟨up[S] μ₁, up_lt₁⟩,
        from @eq_out_of_sigma _ S _ (out ⟨μ₁, lt₁⟩ :: μ₁) μ₂ (suffix_out_cons ⟨μ₁, lt₁⟩)
        (up[S] μ₁) (by simp[eqn_lam₁]) up_lt₁ (by simp[out_eq, Tree'.is_sigma, A]),
      have sigma : (out ⟨up[S] μ₁, up_lt₁⟩).is_sigma,
      { simp[←this, out_eq, Tree'.is_sigma, A] },
      have C₂ := S.up_eq_or_lt μ₂, rcases C₂ with (eqn | ⟨lt', pi⟩),
      { simp[eqn] at up_lt, contradiction },
      { simp[←eqn] at pi lt', exact neg_is_pi_iff.mpr sigma pi } } }
end

-- Consistency 2

lemma sigma_outcome_of_eq_up {μ₁ μ₂ : Tree k} (lt : μ₁ ⊂ᵢ μ₂)
  (eqn : up[S] μ₁ = up[S] μ₂) (up_lt : up[S] μ₂ ⊂ᵢ λ[S] μ₂) : (out ⟨μ₁, lt⟩).is_sigma :=
sigma_outcome_of_eq_up S ((default _) :: μ₂) lt (by simp) eqn up_lt

lemma sigma_outcome_of_pi {μ μ₀ : Tree k} {lt : μ₀ ⊂ᵢ μ} (pi : (out ⟨μ₀, lt⟩).is_pi) :
  λ[S] (out ⟨μ₀, lt⟩ :: μ₀) = (out ⟨μ₀, lt⟩ :: μ₀) :: up[S] μ₀ :=
begin
  simp[lambda, approx.lambda],
  have : up[S] μ₀ ⊂ᵢ λ[S] μ₀ ∨ up[S] μ₀ = λ[S] μ₀,
    from list.suffix_iff_is_initial.mp (S.up_le_lambda μ₀),
  rcases this with (lt_up | eq_up),
  { have : approx.pi_derivative (up[S] μ₀) (S.up' μ₀) = [],
    { simp[approx.pi_derivative, approx.derivative, list.filter_eq_nil],
      rintros ⟨μ₁, lt_μ₁⟩ pi' eq_up,
      have := S.sigma_outcome_of_eq_up lt_μ₁ eq_up lt_up, exact not_pi_sigma pi' this },
    simp [this, pi] },
  { simp[eq_up, lambda] }
end

variables (Λ : Path k)

theorem finite_injury (n : ℕ) :
  ∃ s₀, ∀ s, s₀ ≤ s → λ[S] (Λ s)↾*n = λ[S] (Λ s₀)↾*n :=
begin
  induction n with n IH,
  { simp },
  { rcases IH with ⟨s₀, IH⟩,
    suffices :
      ∃ s₁, s₀ ≤ s₁ ∧ ∀ s, s₁ ≤ s → (λ[S] (Λ s)).rnth n = (λ[S] (Λ s₁)).rnth n,
    { rcases this with ⟨s₁, eqn, hyp_s₁⟩, refine ⟨s₁, λ s eqn_s, _⟩,
      apply list.rnth_ext',
      { intros m a, simp[list.initial_rnth_some_iff], intros eqn_m,
        have C : m < n ∨ m = n, from lt_or_eq_of_le (nat.lt_succ_iff.mp eqn_m),
        cases C,
        { have : (λ[S] (Λ s)↾*n).rnth m = (λ[S] (Λ s₀)↾*n).rnth m,
            from congr_arg (λ l : list _, l.rnth m) (IH s (eqn.trans eqn_s)),
          simp [list.initial_rnth_of_lt C] at this, simp[this],
          have : (λ[S] (Λ s₁)↾*n).rnth m = (λ[S] (Λ s₀)↾*n).rnth m,
            from congr_arg (λ l : list _, l.rnth m) (IH s₁ eqn),
          simp [list.initial_rnth_of_lt C] at this, simp[this] },
        { simp[C], have := hyp_s₁ s eqn_s, simp[this] } } },
    by_cases C₁ : ∀ s, s₀ ≤ s → (λ[S] (Λ s)).rnth n = none,
    { refine ⟨s₀, by refl, λ s eqn_s, _⟩, simp[C₁ s eqn_s, C₁ s₀ (by refl)] },
    { have : ∃ s₁, s₀ ≤ s₁ ∧ ∃ x, (λ[S] (Λ s₁)).rnth n = some x,
      { simp at C₁, rcases C₁ with ⟨s₁, eqn, C₁⟩, exact ⟨s₁, eqn, option.ne_none_iff_exists'.mp C₁⟩ },
      rcases this with ⟨s₁, eqn_s₁, ν, C₁⟩,
      have IH' : ∀ (s : ℕ), s₁ ≤ s → λ[S] (Λ s)↾*n = λ[S] (Λ s₁)↾*n, 
      { intros s le, simp[IH s₁ eqn_s₁, IH s (eqn_s₁.trans le)] },
      have lt : λ[S] (Λ s₁)↾*n ⊂ᵢ λ[S] (Λ s₁),
        from list.suffix_cons_iff_is_initial.mp ⟨_, list.rnth_eq_iff_suffix_cons_initial.mp C₁⟩,
      have lt' : ∀ s, s₁ ≤ s → λ[S] (Λ s₁)↾*n ⊂ᵢ λ[S] (Λ s),
      { intros s eqn_s, refine S.lt_lambda_of_lt_le (Λ.mono' eqn_s) lt
        (by { simp[←IH' s eqn_s], exact list.suffix_initial _ _}) },
      have rnth_eqn : ∀ s (le : s₁ ≤ s), (λ[S] (Λ s)).rnth n = some (out ⟨λ[S] (Λ s₁)↾*n, lt' s le⟩),
      { intros s le, refine list.rnth_eq_iff_suffix_cons_initial.mpr _, have := suffix_out_cons ⟨_, lt' s le⟩,
        simp[IH' s le], exact this },
      by_cases C₂ : ∀ (s : ℕ) (le : s₁ ≤ s), (out ⟨λ[S] (Λ s₁)↾*n, lt' s le⟩).is_pi,
      { refine ⟨s₁, eqn_s₁, λ s eqn_s, _⟩, simp[rnth_eqn, rnth_eqn _ eqn_s],
        refine eq.symm (S.eq_out_of_pi (Λ.mono' eqn_s) _ _ (by simp[C₂])) },
      { have : ∃ s₂ (h : s₁ ≤ s₂), ↥((out ⟨λ[S] (Λ s₁)↾*n, lt' s₂ h⟩).is_sigma),
        { simp at C₂, exact C₂ },
        rcases this with ⟨s₂, eqn_s₂, C₂⟩,
        refine ⟨s₂, eqn_s₁.trans eqn_s₂, λ s eqn_s, _⟩, simp[rnth_eqn _ eqn_s₂, rnth_eqn _ (eqn_s₂.trans eqn_s)], 
        refine eq.symm (S.eq_out_of_sigma (Λ.mono' eqn_s) _ _ C₂) } } }
end

theorem Path_exists :
  ∃ Λ' : Path (k + 1), ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → λ[S] (Λ s)↾*n = Λ' n :=
begin
  let P : ℕ → ℕ → Prop := λ n s₀, (∀ s, s₀ ≤ s → λ[S] (Λ s)↾*n = λ[S] (Λ s₀)↾*n),
  have : ∀ n, ∃ s₀, P n s₀, from λ n, S.finite_injury Λ n,
  have : ∀ n, ∃ s₀, (∀ s, s < s₀ → ¬P n s) ∧ P n s₀,
  { intros n, exact nat.least_number (this n) },
  have : ∃ (f : ℕ → ℕ), ∀ x, (∀ s, s < f x → ¬P x s) ∧ P x (f x),
    from classical.skolem.mp this,
  rcases this with ⟨f, h_f⟩,
  let path : ℕ → Tree (k + 1) := λ n, λ[S] (Λ (f n))↾*n,
  have mono : ∀ n, path n <:+ path (n + 1),
  { intros n, simp[path],
    have mono : f n ≤ f (n + 1),
    { suffices : ¬f (n + 1) < f n, { simp* at* },
      intros A,
      have min : ∃ x, f (n + 1) ≤ x ∧ ¬λ[S] (Λ x)↾*n = λ[S] (Λ (f (n + 1)))↾*n,
      { have := (h_f n).1 _ A, simp[P] at this, exact this },
      rcases min with ⟨m, le_m, neq⟩,
      have : λ[S] (Λ m)↾*(n + 1) = λ[S] (Λ (f (n + 1)))↾*(n + 1),
      { have := (h_f (n + 1)).2 _ le_m, exact this },
      have := (congr_arg (λ l : list _, l↾*n) this), simp at this, exact neq this },
    have : λ[S] (Λ (f (n + 1)))↾*n = λ[S] (Λ (f n))↾*n, from (h_f n).2 _ mono, 
    simp[←this],
    rw (show λ[S] (Λ (f (n + 1)))↾*n = λ[S] (Λ (f (n + 1)))↾*(n + 1)↾*n, by simp),
    exact list.suffix_initial _ _ },
  refine ⟨⟨path, mono⟩, λ n, ⟨f n, λ s eqn_s, _⟩⟩,
  exact (h_f n).2 _ eqn_s
end

noncomputable def Lambda (Λ : Path k) : Path (k + 1) := classical.epsilon
(λ Λ',  ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → λ[S] (Λ s)↾*n = Λ' n)

notation `Λ[` S `]` := Lambda S

theorem Lambda_spec : ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → λ[S] (Λ s)↾*n = (Λ[S] Λ) n :=
classical.epsilon_spec (S.Path_exists Λ)

lemma lt_Lambda_iff {Λ : Path k} {η : Tree (k + 1)} :
  η ⊂' Λ[S] Λ ↔ ∃ s₀, ∀ s, s₀ ≤ s → η ⊂ᵢ λ[S] (Λ s) :=
⟨λ ⟨n, h⟩, by {
    rcases S.Lambda_spec Λ n with ⟨s₀, eqn⟩,
    refine ⟨s₀, λ s eqn_s, _⟩,
    have : λ[S] (Λ s)↾*n = (Λ[S] Λ) n, from eqn s eqn_s, simp[←this] at h,
    have : λ[S] (Λ s)↾*n <:+ λ[S] (Λ s), from list.suffix_initial _ _,
    exact list.is_initial.is_initial_of_suffix h this }, 
  λ ⟨s₀, h⟩, by { 
    rcases S.Lambda_spec Λ (η.length + 1) with ⟨s₁, eqn⟩,
    refine ⟨η.length + 1, _⟩,
    have := eqn (max s₀ s₁) (le_max_right s₀ s₁), rw ←this,
    rcases h (max s₀ s₁) (le_max_left s₀ s₁) with ⟨l, a, eqn⟩,
    simp[←eqn, list.initial] }⟩

lemma le_lamvda_of_lt_Lambda' {Λ : Path k} {η : Tree (k + 1)} {s₀} (lt : η ⊂ᵢ (Λ[S] Λ) s₀) :
  ∃ s₁, ∀ s, s₁ ≤ s → out ⟨η, lt⟩ :: η <:+ λ[S] (Λ s) :=
begin
  rcases S.Lambda_spec Λ s₀ with ⟨s₁, eqn⟩, refine ⟨s₁, λ s le_s, _⟩,
  have : out ⟨η, lt⟩ :: η <:+ λ[S] (Λ s)↾*s₀, simp[eqn s le_s], from suffix_out_cons ⟨η, lt⟩,
  exact this.trans (list.suffix_initial (lambda S (Λ s)) s₀)
end

lemma le_Lambda_of_thick {Λ : Path k} (thick : Λ.thick)
  {η : Tree (k + 1)} {s₀} (le : η <:+ (Λ[S] Λ) s₀) : lim s, η =≤ λ[S] (Λ s) :=
begin
  rcases S.Lambda_spec Λ s₀ with ⟨t, eqn⟩,
  have le' : ∀ s, t ≤ s → η <:+ λ[S] (Λ s),
  { intros s le_s,
    have : (Λ[S] Λ) s₀ <:+ λ[S] (Λ s), { simp[←eqn s le_s], exact list.suffix_initial _ _ },
    exact le.trans this },
  rcases S.eq_lambda_of_le_lambda' (le' t (by refl)) with ⟨μ₁, le_μ₁, rfl⟩,
  rcases thick.ssubset.mp ⟨t, le_μ₁⟩ with ⟨s₁, rfl⟩,
  have : ∀ s, s₁ ≤ s → λ[S] (Λ s₁) <:+ λ[S] (Λ s),
  { intros s le_s, have C : s ≤ t ∨ t ≤ s, exact le_total s t,
    cases C,
    { exact S.suffix_of_suffix (Λ.mono' le_s) (Λ.mono' C) (le' t (by refl)) },
    { exact le' s C } },
  refine ⟨s₁, rfl, this⟩
end

lemma eq_lt_lambda_of_lt_Lambda_of_pi {Λ : Path k} (thick : Λ.thick)
  {η : Tree (k + 1)} {s₀} (lt : η ⊂ᵢ (Λ[S] Λ) s₀) (pi : (out ⟨η, lt⟩).is_pi) :
  lim s, ⟨η, lt⟩ =< λ[S] (Λ s) :=
begin
  rcases S.le_Lambda_of_thick thick (suffix_out_cons ⟨η, lt⟩) with ⟨s₁, eqn₁, le₁⟩, simp at eqn₁ le₁,
  rcases S.le_Lambda_of_thick thick (lt.suffix) with ⟨s₂, rfl, le₂⟩, 
  have : ∃ s, s₂ ≤ s ∧ λ[S] (Λ s₂) = λ[S] (Λ s) ∧ λ[S] (Λ s₂) ⊂ᵢ λ[S] (Λ (s + 1)),
  { by_contradiction,
    simp at h,
    have : ∀ s, s₂ ≤ s → λ[S] (Λ s₂) = λ[S] (Λ s) → λ[S] (Λ s₂) = λ[S] (Λ (s + 1)),
    { intros s le eqn,
      have : ¬λ[S] (Λ s₂) ⊂ᵢ λ[S] (Λ (s + 1)), from h s le eqn,
      rcases list.suffix_iff_is_initial.mp (le₂ (s + 1) (le_add_right le)) with (lt_lam | eq_lam),
      { exfalso, exact this lt_lam }, { exact eq_lam } },
    have eq_lam' : ∀ s, s₂ ≤ s → λ[S] (Λ s₂) = λ[S] (Λ s),
    { suffices : ∀ s, λ[S] (Λ s₂) = λ[S] (Λ (s₂ + s)),
      { intros s le,
        simp[this (s - s₂), show  s₂ + (s - s₂) = s, from nat.add_sub_of_le le] },
      intros s, induction s with s IH,
      { refl }, { simp[←nat.add_one, ←add_assoc], exact this (s₂ + s) (le_self_add) IH } },
    have lt_lam : λ[S] (Λ s₂) ⊂ᵢ λ[S] (Λ (max s₁ s₂)),
      from list.suffix_cons_iff_is_initial.mp ⟨_, le₁ (max s₁ s₂) (le_max_left s₁ s₂)⟩,
    have eq_lam : λ[S] (Λ s₂) = λ[S] (Λ (max s₁ s₂)), from eq_lam' (max s₁ s₂) (le_max_right s₁ s₂),
    simp[eq_lam] at lt_lam, contradiction },
  rcases this with ⟨s₃, le_s₃, eq_lam_s₂, lt_lam_s₂⟩,
  have : ∀ s, s₃ ≤ s → out ⟨λ[S] (Λ s₂), lt⟩ :: λ[S] (Λ s₂) <:+ λ[S] (Λ (s + 1)),
  { intros s le_s, have C : s₁ ≤ s ∨ s < s₁, exact le_or_lt s₁ s, cases C,
    { exact le₁ (s + 1) (le_add_right C) }, 
    { have lt₁ : λ[S] (Λ s₂) ⊂ᵢ λ[S] (Λ s.succ),
      { rcases list.suffix_iff_is_initial.mp (le₂ (s + 1) (le_add_right (le_s₃.trans le_s))) with (C | C); simp at C,
        { exact C }, { exfalso, simp[C] at lt_lam_s₂, refine S.noninitial_of_suffix (Λ.mono' (by simp[le_s])) lt_lam_s₂ } },
      have lt₂ : λ[S] (Λ s₂) ⊂ᵢ λ[S] (Λ s₁), from list.suffix_cons_iff_is_initial.mp ⟨_, le₁ s₁ (by refl)⟩,
      have eqn₁ : out ⟨λ[S] (Λ s₂), lt₂⟩ = out ⟨λ[S] (Λ s₂), lt⟩, { simp[out_eq_iff], exact le₁ s₁ (by refl) },      
      have eqn₂ : out ⟨λ[S] (Λ s₂), lt₁⟩ = out ⟨λ[S] (Λ s₂), lt₂⟩, 
        from S.eq_out_of_pi (Λ.mono' (nat.succ_le_iff.mpr C)) lt₁ lt₂ (by simp[eqn₁]; exact pi),
      simp[←eqn₁, ←eqn₂], exact suffix_out_cons ⟨λ[S] (Λ s₂), lt₁⟩ } },
  refine ⟨s₃, eq_lam_s₂, this⟩  
end

lemma equiv_lambda {Λ₁ Λ₂ : Path k} (equiv : Λ₁ ≃ₚ Λ₂) :
  Λ[S] Λ₁ = Λ[S] Λ₂ :=
Path.ext (λ s, begin
  rcases S.Lambda_spec Λ₁ s with ⟨t₁, eqn₁⟩,
  have : ∃ μ₁, μ₁ <:+ Λ₁ t₁ ∧ (Λ[S] Λ₁) s = λ[S] μ₁,
    simp [←eqn₁ t₁ (by refl)], from S.eq_lambda_of_le_lambda' (list.suffix_initial _ _),
  rcases this with ⟨μ₁, le₁, eqn_lam₁⟩,    
  rcases equiv.1 t₁ with ⟨s₂, le₂⟩,
  rcases equiv.2 s₂ with ⟨s₃, le₃⟩,
  have le₃' : Λ₂ s₂ <:+ Λ₁ (max t₁ s₃), from le₃.trans (Λ₁.mono' (le_max_right t₁ s₃)),
  have : λ[S] μ₁ <:+ λ[S] (Λ₁ (max t₁ s₃)),
  { simp[←eqn_lam₁, ←eqn₁ (max t₁ s₃) (le_max_left t₁ s₃)], exact list.suffix_initial _ _ },  
  have : λ[S] μ₁ <:+ λ[S] (Λ₂ s₂), from S.suffix_of_suffix (le₁.trans le₂) le₃' this,
  have : λ[S] (Λ₂ s₂) = (Λ[S] Λ₂) (λ[S] μ₁).length,
  { rcases S.Lambda_spec Λ₂ (λ[S] μ₁).length with ⟨t₂, eqn₂⟩,
    rw ← eqn₂ (max t₂ s₂) (le_max_left t₂ s₂), sorry  },
  rcases S.Lambda_spec Λ₂ s with ⟨t₂, eqn₂⟩,  
  sorry
  
end)

@[simp] def lambda_itr : ∀ (μ : Tree k) (i : ℕ), Tree (k + i)
| μ 0       := μ
| μ (i + 1) := λ[S] (lambda_itr μ i)

@[simp] def up_itr : ∀ (μ : Tree k) (i : ℕ), Tree (k + i)
| μ 0       := μ
| μ (i + 1) := up[S] (up_itr μ i)

lemma lambda_proper {μ : Tree k} (proper : μ.proper) : (λ[S] μ).proper :=
begin
  induction μ with ν μ IH,
  { simp },
  { have C : λ[S] (ν :: μ) = (ν :: μ) :: up[S] μ ∨ λ[S] (ν :: μ) = λ[S] μ, from S.lambda_cons_eq ν μ,
    have proper' : @Tree'.proper (k + 1) μ, exact Tree'.proper.proper_of_cons proper,
    cases C,
    { simp[C, Tree'.proper],
      have lt_of_mem : ∀ η, η ∈ up[S] μ → η ⊂ᵢ ν :: μ,
      { intros η mem,
        have mem' : η ∈ λ[S] μ, { rcases S.up_le_lambda μ with ⟨l, h⟩,simp[←h, mem] },
        exact list.is_initial_cons_iff_suffix.mpr (S.suffix_of_mem_lambda mem') },
      have proper_of_mem : ∀ η : Tree' (k + 1), η ∈ up[S] μ → η.proper,
      { intros η mem,
        have mem' : η ∈ λ[S] μ, { rcases S.up_le_lambda μ with ⟨l, h⟩,simp[←h, mem] },
        exact (IH proper').2 mem' },      
      refine ⟨⟨list.ordered_suffix (S.up_le_lambda μ) ((IH proper').1), lt_of_mem⟩, proper, proper_of_mem⟩ },
    { simp[C], exact IH proper' } }
end

lemma up_proper {μ : Tree k} (proper : μ.proper) : (up[S] μ).proper :=
Tree'.proper.proper_of_le (S.up_le_lambda μ) (S.lambda_proper proper)

lemma weight_lambda_mono {μ₁ μ₂ : Tree k} (lt : μ₁ ⊂ᵢ μ₂) (ne : λ[S] μ₁ ≠ λ[S] μ₂) :
  (λ[S] μ₁).weight < (λ[S] μ₂).weight :=
begin
  cases eqn₁ : λ[S] μ₁ with π η₁;
  cases eqn₂ : λ[S] μ₂ with σ η₂,
  { simp [eqn₁, eqn₂] at ne, contradiction },
  { simp },
  { exfalso, have := S.noninitial_of_suffix (list.suffix_of_is_initial lt), simp[eqn₁, eqn₂] at this, contradiction },
  have le₁ : π <:+ μ₁, from  S.suffix_of_mem_lambda (by simp[eqn₁]),
  have le₂ : σ <:+ μ₂, from  S.suffix_of_mem_lambda (by simp[eqn₂]),
  have le₁' : π <:+ μ₂, from list.suffix_of_is_initial (list.is_suffix.is_initial_of_is_initial le₁ lt),
  have eqn_lam₁ : λ[S] π = λ[S] μ₁, from S.eq_lambda_of_pred eqn₁,
  have eqn_lam₂ : λ[S] σ = λ[S] μ₂, from S.eq_lambda_of_pred eqn₂,
  have C : π ⊂ᵢ σ ∨ π = σ ∨ σ ⊂ᵢ π, from trichotomous_of_le_of_le le₁' le₂,
  cases C,
  { exact lt_weight_cons_of_lt C }, exfalso, rcases C with ⟨rfl, C⟩,
  { simp[←eqn_lam₁, ←eqn_lam₂] at ne, contradiction },
  { have := S.suffix_of_suffix (list.suffix_of_is_initial C) le₁' (by simp[eqn_lam₂]),
    simp[eqn_lam₁, eqn_lam₂] at this, 
    have C₁ : λ[S] μ₂ ⊂ᵢ λ[S] μ₁ ∨ λ[S] μ₂ = λ[S] μ₁,
      from list.suffix_iff_is_initial.mp this,
    cases C₁, { exact S.noninitial_of_suffix (list.suffix_of_is_initial lt) C₁ },
    { exact ne (eq.symm C₁)} }
end

lemma Lambda_pi_outcome
  {η : Tree (k + 1)} {s₀} (lt : η ⊂ᵢ (Λ[S] Λ) s₀) (pi : (out ⟨η, lt⟩).is_pi)
  {μ : Tree k} {t₀} (lt' : μ ⊂ᵢ Λ t₀) (up_eq : up[S] μ = η) : (out ⟨μ, lt'⟩).is_sigma :=
begin
  rcases up_eq with rfl,
  rcases S.le_lamvda_of_lt_Lambda' lt with ⟨s₁, le⟩,
  by_contradiction A, simp at A,
  have eq_lam : λ[S] (out ⟨μ, lt'⟩ :: μ) = (out ⟨μ, lt'⟩ :: μ) :: up[S] μ, 
    from S.sigma_outcome_of_pi A,
  have : out ⟨up[S] μ, lt⟩ = out ⟨μ, lt'⟩ :: μ,
  { have lt₁ : up[S] μ ⊂ᵢ λ[S] (out ⟨μ, lt'⟩ :: μ), { simp[eq_lam] },
    have lt₂ : up[S] μ ⊂ᵢ λ[S] (Λ (max s₁ t₀)),
      from list.suffix_cons_iff_is_initial.mp ⟨_, le (max s₁ t₀) (le_max_left s₁ t₀)⟩,
    have eq_out₁ : out ⟨up[S] μ, lt₁⟩ = out ⟨μ, lt'⟩ :: μ, { simp[out_eq_iff, eq_lam] },
    have eq_out₂ : out ⟨up[S] μ, lt₁⟩ = out ⟨up[S] μ, lt₂⟩,
      from S.eq_out_of_sigma ((suffix_out_cons ⟨μ, lt'⟩).trans (Λ.mono' (le_max_right s₁ t₀))) lt₁ lt₂ (by simp[eq_out₁, A]),
    have : out ⟨up[S] μ, lt₂⟩ = out ⟨up[S] μ, lt⟩,
    { simp[out_eq_iff], exact le (max s₁ t₀) (le_max_left s₁ t₀) },
    rw[←eq_out₁, eq_out₂, this] },
  simp[this] at pi, exact not_pi_sigma A pi
end

lemma Lambda_sigma_outcome
  {η : Tree (k + 1)} {s₀} (lt : η ⊂ᵢ (Λ[S] Λ) s₀) (sigma : (out ⟨η, lt⟩).is_sigma) :
  ∃ {μ : Tree k} {t₀} (lt' : μ ⊂ᵢ Λ t₀) (up_eq : up[S] μ = η), (out ⟨μ, lt'⟩).is_pi :=
begin
  rcases S.le_lamvda_of_lt_Lambda' lt with ⟨s₁, le⟩,
  have lt' : η ⊂ᵢ λ[S] (Λ s₁), from list.suffix_cons_iff_is_initial.mp ⟨_, le s₁ (by refl)⟩,
  rcases S.out_eq_out ⟨η, lt'⟩ with ⟨⟨μ, lt_μ⟩, eqn_μ⟩,
  have eq_out : out ⟨η, lt'⟩ = out ⟨η, lt⟩, { simp[out_eq_iff], exact le s₁ (by refl) },
  have pi : (out ⟨μ, lt_μ⟩).is_pi, { simp[←eq_out, eqn_μ] at sigma, exact sigma },
  have : up[S] μ = η,
  { rcases S.eq_lambda_of_lt_lambda ⟨η, lt'⟩ with ⟨⟨μ₀, lt_μ₀⟩, _, _, eqn_μ₀, eq_up₀⟩, 
    have : μ = μ₀, { simp[eqn_μ] at eqn_μ₀, exact list.tail_eq_of_cons_eq eqn_μ₀ },
    rcases this with rfl, exact eq.symm eq_up₀ },
  exact ⟨μ, s₁, lt_μ, this, pi⟩
end

-- derivatives の候補
def antiderivatives (μ : Tree k) : list (Tree (k + 1) × ℕ) :=
(λ[S] μ, 0) :: ((λ[S] μ).ancestors.filter (λ η, (out η).is_pi)).map (λ η, (η, (S.derivative ↑η μ).length))

lemma Min_antiderivative_eq_assignment (μ : Tree k) :
  (S.priority (k + 1)).Min_le (S.antiderivatives μ) (by simp[antiderivatives]) = S.assignment μ :=
by simp[antiderivatives, assignment, approx.assignment]; refl

@[simp] lemma mem_assignment_antiderivatives (μ : Tree k) :
  S.assignment μ ∈ S.antiderivatives μ := (S.priority (k + 1)).Min_le_mem _

lemma nonsuffix_of_scons (μ₁ μ₂ : Tree k) (lt : μ₁ ⊂ᵢ μ₂) : ¬λ[S] μ₂ <:+ up[S] μ₁ := λ le,
begin
  have C : λ[S] (out ⟨μ₁, lt⟩ :: μ₁) = (out ⟨μ₁, lt⟩ :: μ₁) :: up[S] μ₁ ∨
    (λ[S] (out ⟨μ₁, lt⟩ :: μ₁) = λ[S] μ₁ ∧ up[S] μ₁ ⊂ᵢ λ[S] μ₁),
  { simp[lambda, approx.lambda],
    by_cases C :
      up[S] μ₁ = approx.lambda (S.up' μ₁) ∨ (out ⟨μ₁, lt⟩).is_pi ∧ approx.pi_derivative (up[S] μ₁) (S.up' μ₁) = []; simp[C],
    { simp[not_or_distrib] at C, right, refine list.is_initial_iff_suffix.mpr ⟨up_le_lambda S μ₁, C.1⟩ } },
  rcases C with (C | ⟨C, lt'⟩),
  { have le_out : out ⟨μ₁, lt⟩ :: μ₁ <:+ μ₂, from suffix_out_cons ⟨μ₁, lt⟩,
    have lt : λ[S] μ₂ ⊂ᵢ λ[S] (out ⟨μ₁, lt⟩ :: μ₁), simp[C], from list.is_initial_cons_iff_suffix.mpr le,
    exact noninitial_of_suffix S le_out lt },
  { have := le.is_initial_of_is_initial lt', exact S.noninitial_of_suffix lt.suffix this }
end

lemma le_of_mem_antiderivatives {μ : Tree k} {η : Tree (k + 1)} {n : ℕ} (mem : (η, n) ∈ S.antiderivatives μ) :
  η <:+ λ[S] μ ∧ n = (S.derivative η μ).length :=
begin
  simp[antiderivatives] at mem,
  rcases mem with (⟨rfl, rfl⟩ | ⟨⟨μ₁, lt⟩, pi, rfl, rfl⟩),
  { have : S.derivative (λ[S] μ) μ = [],
    { simp[derivative, approx.derivative, list.filter_eq_nil], rintros ⟨μ₁, lt⟩ eqn,
      have := S.nonsuffix_of_scons _ _ lt (by simp[←eqn]), contradiction },
    simp[this] },
  { simp, exact list.is_initial.suffix lt }
end

lemma assignment_snd_eq (μ : Tree k) : (S.assignment μ).2 = (S.derivative (up[S] μ) μ).length :=
begin
  have : S.assignment μ ∈ _, from omega_ordering.Min_le_mem _ _, simp at this, rcases this with (eqn| ⟨η, pi, eqn⟩),
  { have eqn_lam : up[S] μ = λ[S] μ, from congr_arg prod.fst eqn,
    have : S.derivative (up[S] μ) μ = [],
    { simp[derivative, approx.derivative, list.filter_eq_nil],
      rintros ⟨μ₁, lt⟩ eqn_μ₁,
      exact S.nonsuffix_of_scons _ _ lt (by simp[←eqn_lam, ←eqn_μ₁]) },
    rw[this, eqn], simp },
  have : ↑η = up[S] μ,
  { have : (S.assignment μ).fst = up[S] μ, from S.assignment_fst_eq_up μ, simp[←eqn] at this, exact this },
  simp[←eqn, this], refl 
end

lemma assignment_eq (μ : Tree k) : S.assignment μ = (up[S] μ, (S.derivative (up[S] μ) μ).length) :=
prod.ext (by simp[S.assignment_fst_eq_up μ]) (by simp[assignment_snd_eq])

lemma derivative_mono (η : Tree (k + 1)) {μ₁ μ₂ : Tree k} (le : μ₁ <:+ μ₂) :
  (S.derivative η μ₁).map subtype.val <:+ (S.derivative η μ₂).map subtype.val :=
by { have : ∀ μ, (S.derivative η μ).map subtype.val = ((μ.ancestors.map subtype.val).filter (λ a, up[S] a = η)),
    { intros μ, simp[derivative, approx.derivative], simp[list.map_filter, function.comp], congr },
    simp[this], exact (list.is_suffix.filter _ (ancestor.ancestors'_suffix_of_suffix le)) }

lemma nonmem_antiderivatives {μ₁ μ₂ : Tree k} (lt : μ₁ ⊂ᵢ μ₂) : S.assignment μ₁ ∉ S.antiderivatives μ₂ := λ A,
begin
  simp [antiderivatives] at A, rcases A with (A | ⟨⟨η, lt_η⟩, pi, A⟩),
  { have : up[S] μ₁ = λ[S] μ₂, from congr_arg prod.fst A,
    exact nonsuffix_of_scons S μ₁ μ₂ lt (by simp[this]) },
  { have : η = up[S] μ₁, { have := S.assignment_fst_eq_up μ₁, simp [←A] at this, exact this }, rcases this with rfl,
    have eq : ((S.derivative (up[S] μ₁) μ₂).map subtype.val).length = ((S.derivative (up[S] μ₁) μ₁).map subtype.val).length,
    { have := S.assignment_snd_eq μ₁, simp [←A] at this, simp[this] },
    have neq : (S.derivative (up[S] μ₁) μ₁).map subtype.val ≠ (S.derivative (up[S] μ₁) μ₂).map subtype.val,
    { intros eqn_der,
      have : μ₁ ∈ (S.derivative (up[S] μ₁) μ₁).map subtype.val,
      { rw eqn_der, simp[derivative, approx.derivative], exact ⟨⟨μ₁, lt⟩, rfl, rfl⟩ },
      have : μ₁ ∉ (S.derivative (up[S] μ₁) μ₁).map subtype.val,
      { simp[derivative, approx.derivative], rintros ⟨μ₂, lt⟩ _ eqn, simp[←eqn] at lt, contradiction },
      contradiction },
    have : (S.derivative (up[S] μ₁) μ₁).map subtype.val ⊂ᵢ (S.derivative (up[S] μ₁) μ₂).map subtype.val,
      from list.is_initial_iff_suffix.mpr ⟨S.derivative_mono (up[S] μ₁) lt.suffix, neq⟩,
    have : ((S.derivative (up[S] μ₁) μ₁).map subtype.val).length < ((S.derivative (up[S] μ₁) μ₂).map subtype.val).length,
      from list.is_initial_length this,
    simp[eq] at this, contradiction }
end

lemma case_mem_antiderivative {μ : Tree k} {ν : Tree' k} (η : Tree (k + 1)) (n : ℕ) (lt : η ⊂ᵢ λ[S] (ν :: μ))
  (pi : (out ⟨η, lt⟩).is_pi)
  (mem : (η, n) ∈ S.antiderivatives μ) :
  (η, n) = S.assignment μ ∧ (η, n + 1) ∈ S.antiderivatives (ν :: μ) ∨ 
  (η, n) ≠ S.assignment μ ∧ (η, n) ∈ S.antiderivatives (ν :: μ) :=
begin
  have der : n = (S.derivative η μ).length, from (S.le_of_mem_antiderivatives mem).2,
  simp[antiderivatives] at mem ⊢, rcases mem with (⟨rfl, rfl⟩ | ⟨⟨η₁, lt'⟩, pi, rfl, rfl⟩),
  { by_cases C :
      up[S] μ = λ[S] μ ∨ ν.is_pi ∧ approx.pi_derivative (up[S] μ) (S.up' μ) = list.nil,
    { have eqn : λ[S] (ν :: μ) = (ν :: μ) :: up[S] μ, { unfold lambda at*, simp[approx.lambda, C] },
      cases C,
      { left, simp[assignment_eq, C, der],
        have lt : λ[S] μ ⊂ᵢ λ[S] (ν :: μ), { simp[eqn, C] },
        refine ⟨⟨λ[S] μ, lt⟩, _⟩, simp,
        have eqn_der : S.derivative (λ[S] μ) (ν :: μ) = [⟨μ, by simp⟩],
        { simp[derivative_cons, C], exact list.length_eq_zero.mp (eq.symm der) },
        simp[eqn_der, pi, ←der] },
      { exfalso,
        have :  λ[S] μ ⊂ᵢ (ν :: μ) :: up[S] μ, simp[←eqn, lt],
        have : λ[S] μ = up[S] μ,
        { have C₁ := list.is_initial_cons_iff.mp this, 
          cases C₁, { exact C₁ }, { exfalso, exact list.is_initial_suffix_antisymm C₁ (S.up_le_lambda _) } },
        have : out ⟨λ[S] μ, lt⟩ = ν :: μ, { simp[out_eq_iff, this, eqn] },
        simp[this] at pi, exact not_pi_sigma C.1 pi } },
    { have eqn : λ[S] (ν :: μ) = λ[S] μ, { unfold lambda at*, simp[approx.lambda, C] },
      have ne_up : ¬up[S] μ = λ[S] μ, { simp[not_or_distrib] at C, exact C.1 },
      right,
      simp[assignment_eq, eqn], intros h, have := eq.symm h, contradiction } },
  { by_cases C : up[S] μ = η₁,
    { left, simp[assignment_eq, C], refine ⟨⟨η₁, lt⟩, pi, rfl, by simp[derivative_cons, C]⟩ },
    { right, simp[assignment_eq, C],
      exact ⟨λ h, by exfalso; exact C (eq.symm h), or.inr ⟨⟨η₁, lt⟩, pi, rfl, by simp[derivative_cons, C]⟩⟩ } }
end

lemma infinite_substrategy_of_pi
  (thick : Λ.thick) {η : Tree (k + 1)} (s₀) (lt : η ⊂ᵢ (Λ[S] Λ) s₀) (pi : (out ⟨η, lt⟩).is_pi) (n) :
  ∃ s, (η, n) = S.assignment (Λ s) :=
begin
  rcases S.eq_lt_lambda_of_lt_Lambda_of_pi thick lt pi with ⟨s₁, eqn_η, le⟩, simp at eqn_η,
  suffices : ∃ s, s₁ ≤ s ∧ (η, n) = S.assignment (Λ s), { rcases this with ⟨s, _, eqn⟩, exact ⟨s, eqn⟩ },
  induction n with n IH,
  { have mem : (η, 0) ∈ S.antiderivatives (Λ s₁), { simp[antiderivatives, eqn_η], },
    have mem_of_ne : ∀ s, 
      (η, 0) ≠ S.assignment (Λ (s₁ + s)) →
      (η, 0) ∈ S.antiderivatives (Λ (s₁ + s)) →
      (η, 0) ∈ S.antiderivatives (Λ (s₁ + s + 1)),
    { intros s neq mem,   
      rcases thick.2 (s₁ + s) with ⟨ν, eqn_path⟩,
      have lt' : η ⊂ᵢ λ[S] (ν :: Λ (s₁ + s)),
      { simp[←eqn_path], exact list.suffix_cons_iff_is_initial.mp ⟨_, le (s₁ + s) (le_self_add)⟩ },
      have : out ⟨η, lt'⟩ = out ⟨η, lt⟩, { simp[out_eq_iff, ←eqn_path], exact le (s₁ + s) (le_self_add) },
      have := S.case_mem_antiderivative η 0 lt' (by simp[this]; exact pi) mem,
      simp[neq, ←eqn_path] at this, exact this },
    have : ∃ s, (η, 0) = S.assignment (Λ (s₁ + s)),
      from (S.priority (k + 1)).eq_Min_sequence (λ s, S.antiderivatives (Λ (s₁ + s))) (by simp[antiderivatives])
        (λ s t lt, S.nonmem_antiderivatives (thick.is_initial_of_lt (add_lt_add_left lt s₁))) mem mem_of_ne,
    rcases this with ⟨s, eqn⟩, exact ⟨s₁ + s, le_self_add, eqn⟩ },
  { rcases IH with ⟨s₂, le_s₂, eqn_IH⟩,
    have mem : (η, n + 1) ∈ S.antiderivatives (Λ (s₂ + 1)),
    { rcases thick.2 s₂ with ⟨ν, eqn_path⟩,
      have lt' : η ⊂ᵢ λ[S] (ν :: Λ s₂),
      { simp[←eqn_path], exact list.suffix_cons_iff_is_initial.mp ⟨_, le s₂ le_s₂⟩ },
      have : out ⟨η, lt'⟩ = out ⟨η, lt⟩, { simp[out_eq_iff, ←eqn_path], exact le s₂ le_s₂ },
      have : (η, n) = S.assignment (Λ s₂) ∧ (η, n + 1) ∈ S.antiderivatives (ν :: Λ s₂) ∨
             (η, n) ≠ S.assignment (Λ s₂) ∧ (η, n)     ∈ S.antiderivatives (ν :: Λ s₂),
        from S.case_mem_antiderivative η n lt' (by simp[this]; exact pi) (by simp[eqn_IH]),
      simp[eqn_IH, ←eqn_path] at this, exact this },
    have mem_of_ne : ∀ s, 
      (η, n + 1) ≠ S.assignment (Λ (s₂ + 1 + s)) →
      (η, n + 1) ∈ S.antiderivatives (Λ (s₂ + 1 + s)) →
      (η, n + 1) ∈ S.antiderivatives (Λ (s₂ + 1 + s + 1)),
    { intros s ne mem,
      rcases thick.2 (s₂ + 1 + s) with ⟨ν, eqn_path⟩,
      have lt' : η ⊂ᵢ λ[S] (ν :: Λ (s₂ + 1 + s)),
      { simp[←eqn_path], exact list.suffix_cons_iff_is_initial.mp ⟨_, le (s₂ + 1 + s) (by simp[add_assoc]; exact le_add_right le_s₂)⟩ },
      have : out ⟨η, lt'⟩ = out ⟨η, lt⟩,
      { simp[out_eq_iff, ←eqn_path], exact le (s₂ + 1 + s) (by simp[add_assoc]; exact le_add_right le_s₂) },
      have := S.case_mem_antiderivative η (n + 1) lt' (by simp[this]; exact pi) mem,
      simp[ne, ←eqn_path] at this, exact this },    
    have : ∃ s, (η, n + 1) = S.assignment (Λ (s₂ + 1 + s)),
      from (S.priority (k + 1)).eq_Min_sequence (λ s, S.antiderivatives (Λ (s₂ + 1 + s))) (by simp[antiderivatives])
        (λ s t lt, S.nonmem_antiderivatives (thick.is_initial_of_lt (add_lt_add_left lt (s₂ + 1)))) mem mem_of_ne,
    rcases this with ⟨s, eqn⟩,
    exact ⟨s₂ + 1 + s, (by simp[add_assoc]; exact le_add_right le_s₂), eqn⟩ }
end

lemma Lambda_infinite
  (thick : Λ.thick) : (Λ[S] Λ).infinite := λ s₀,
begin
  rcases S.Lambda_spec Λ s₀ with ⟨s₁, eqn₁⟩,
  rcases S.Lambda_spec Λ (s₀ + 1) with ⟨s₂, eqn₂⟩,
  by_contradiction A, simp at A,
  have eq_Lambda : ∀ s, (Λ[S] Λ) s₀ = (Λ[S] Λ) (s₀ + s),
  { intros s,
    have : (Λ[S] Λ) s₀ <:+ (Λ[S] Λ) (s₀ + s), from (Λ[S] Λ).mono' (le_self_add),
    rcases list.suffix_iff_is_initial.mp this with (lt | eq), { exfalso, exact A s lt }, { exact eq } },
  have le_length : ∀ s, s₂ ≤ s → (λ[S] (Λ s)).length ≤ s₀ + 1,
  { intros s le_s,
    have C : (λ[S] (Λ s)).length ≤ s₀ + 1 ∨ s₀ + 1 < (λ[S] (Λ s)).length, from le_or_lt _ _,
    rcases C, { exact C },
    { exfalso, have := list.initial_length C,
      have eqn_s₀ : ((Λ[S] Λ) s₀).length = s₀ + 1, { simp[eq_Lambda 1, ←eqn₂ s le_s, this] },
      have le_s₀  : ((Λ[S] Λ) s₀).length ≤ s₀, { simp[←eqn₁ s₁ (by refl)] },
      simp[eqn_s₀] at le_s₀, contradiction } },
  have eq_lam : ∀ s, λ[S] (Λ (s₂ + s)) = λ[S] (Λ s₂),
  { intros s, have := eqn₂ s₂ (by refl),
    have : ∀ s, λ[S] (Λ (s₂ + s)) = (Λ[S] Λ) (s₀ + 1),
    { intros s, have := list.initial_elim (le_length (s₂ + s) (le_self_add)),
      simp[←eqn₂ (s₂ + s) (le_self_add), this] },
    simp[this], exact eq.symm (this 0) },
  have mem : (λ[S] (Λ s₂), 0) ∈ S.antiderivatives (Λ s₂), { simp[antiderivatives] },
  have mem_of_ne : ∀ s,
    (λ[S] (Λ s₂), 0) ≠ S.assignment (Λ (s₂ + s)) →
    (λ[S] (Λ s₂), 0) ∈ S.antiderivatives (Λ (s₂ + s)) →
    (λ[S] (Λ s₂), 0) ∈ S.antiderivatives (Λ (s₂ + s + 1)),
  { intros s ne mem, simp[antiderivatives], exact or.inl (eq.symm (eq_lam (s + 1))) },
  have : ∃ s, (λ[S] (Λ s₂), 0) = S.assignment (Λ (s₂ + s)),
    from (S.priority (k + 1)).eq_Min_sequence (λ s, S.antiderivatives (Λ (s₂ + s)))
      (by simp[antiderivatives])
      (λ s t lt, S.nonmem_antiderivatives (thick.is_initial_of_lt (add_lt_add_left lt s₂))) mem mem_of_ne,
  rcases this with ⟨s₃, eqn_assn⟩,
  have eq_up: λ[S] (Λ (s₂ + s₃)) = up[S] (Λ (s₂ + s₃)),
  { have := S.assignment_fst_eq_up (Λ (s₂ + s₃)), rw[←eqn_assn, ←eq_lam s₃] at this, exact this },
  rcases thick.2 (s₂ + s₃) with ⟨ν, eqn_path⟩,
  have : λ[S] (Λ (s₂ + s₃ + 1)) = Λ (s₂ + s₃ + 1) :: λ[S] (Λ (s₂ + s₃)),
  { simp[eqn_path, lambda, approx.lambda, ←eq_up] },
  simp[show λ[S] (Λ (s₂ + s₃ + 1)) = λ[S] (Λ s₂), from eq_lam (s₃ + 1),
    eq_lam s₃] at this, contradiction
end

end strategy

namespace friedberg_muchnik

def str : strategy 1 := default _

def generator : ℕ → (Tree 0 × (list ℕ × list ℕ))
| 0       := ([], [], [])
| (s + 1) :=
    let μ  : Tree 0 := (generator s).1, 
        I₀ : list ℕ := (generator s).2.1,
        I₁ : list ℕ := (generator s).2.2,
        η  : Tree 1 := str.up μ in
    match s.bodd with
    | ff := if ⟦η.length⟧ᵪ^I₀.chr [μ.weight] η.weight = some ff then (∞ :: μ, (I₀, η.weight :: I₁)) else (𝟘 :: μ, (I₀, I₁))
    | tt := if ⟦η.length⟧ᵪ^I₁.chr [μ.weight] η.weight = some ff then (∞ :: μ, (η.weight :: I₀, I₁)) else (𝟘 :: μ, (I₀, I₁))
    end

def Λ₀ : Path 0 := ⟨λ s, (generator s).fst, λ s,
  by { cases C : s.bodd; simp[generator, C],
       { by_cases C₁ : ⟦(up[str] (generator s).fst).length⟧ᵪ^((generator s).2.1.chr) [(generator s).1.weight]
         (up[str] (generator s).1).weight = some ff; simp[C₁] },
       { by_cases C₁ : ⟦(up[str] (generator s).fst).length⟧ᵪ^((generator s).2.2.chr) [(generator s).1.weight]
         (up[str] (generator s).1).weight = some ff; simp[C₁] } }⟩

lemma Λ₀_thick : Λ₀.thick :=
⟨by simp[Λ₀, generator], λ s, by { cases C : s.bodd; simp[Λ₀, generator, C],
  { by_cases C₁ : ⟦(up[str] (generator s).fst).length⟧ᵪ^((generator s).2.1.chr) [(generator s).1.weight]
      (up[str] (generator s).1).weight = some ff; simp[C₁], { refine ⟨_, rfl⟩ }, { refine ⟨_, rfl⟩ } },
  { by_cases C₁ : ⟦(up[str] (generator s).fst).length⟧ᵪ^((generator s).2.2.chr) [(generator s).1.weight]
      (up[str] (generator s).1).weight = some ff; simp[C₁], { refine ⟨_, rfl⟩ }, { refine ⟨_, rfl⟩ } } }⟩

lemma Λ₀_app_eq (s : ℕ) : Λ₀ s = (generator s).1 := rfl

def I₀ (s : ℕ) : list ℕ := (generator s).2.1

def I₁ (s : ℕ) : list ℕ := (generator s).2.2

def I₀_inf : set ℕ := {n | ∃ s, n ∈ I₀ s}

def I₁_inf : set ℕ := {n | ∃ s, n ∈ I₁ s}

lemma pi_outcome_even {s₀} (μ : Tree 0) (h : μ ⊂ᵢ Λ₀ s₀) (pi : (out ⟨μ, h⟩).is_pi) (even : μ.length.bodd = ff) :
  ⟦(up[str] μ).length⟧ᵪ^(I₀ μ.length).chr [μ.weight] (up[str] μ).weight = ff ∧ (up[str] μ).weight ∈ I₀ (μ.length + 1):=
begin
  rcases Λ₀_thick.ssubset.mp ⟨_, h.suffix⟩ with ⟨s₁, rfl⟩,
  simp [Λ₀_thick.length] at even, simp at pi,
  have : generator (s₁ + 1) = (∞ :: Λ₀ s₁, (I₀ s₁, (up[str] (Λ₀ s₁)).weight :: (I₁ s₁))),
  { have : Λ₀ (s₁ + 1) = ∞ :: Λ₀ s₁, {  }  }
end



end friedberg_muchnik