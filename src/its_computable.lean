import its reducibility

open encodable denumerable

attribute [simp] set.set_of_app_iff

variables {n : ℕ} (S : strategy n) {k : ℕ}
namespace strategy.aprrox_aux

end strategy.aprrox_aux
open strategy encodable

def ancestor.equiv_fin {k : ℕ} (η : Tree k) :
ancestor η ≃ fin η.length :=
{ to_fun := (λ μ, ⟨μ.val.length, list.is_initial_length μ.property⟩),
  inv_fun := (λ n, ⟨η↾*n.val, list.is_initial_initial η n.val n.property⟩),
  left_inv := (λ ⟨μ, ⟨l, x, p⟩⟩,
    by { simp[←p],  simp only [show l ++ x :: μ = (l ++ [x]) ++ μ, by simp, list.initial_append] }),
  right_inv := (λ ⟨n, lt⟩, by { simp, exact list.initial_length lt }) }

instance primcodable.ancestor_arrow {α : Type*} [primcodable α] {k} (η : Tree k) : primcodable (ancestor η → α) :=
primcodable.of_equiv (fin η.length → α) (equiv.arrow_congr (ancestor.equiv_fin η) (by refl))

def ancestor.extend_fn'_enc (α : Type*) [inhabited α] [primcodable α] (η : Tree k) (x : Tree' k) (n : ℕ) : ℕ := 
  let f := (decode (ancestor (x :: η) → α) n).iget in
encode (ancestor.extend_fn f η (list.suffix_cons x η))

namespace strategy

namespace approx_enc

def derivative (η : Tree (k + 1)) (μ : Tree k) (υ : list (Tree (k + 1))) : list ℕ :=
(list.range_r μ.length).filter (λ i, υ.nth i = η)

def pi_derivative
  (η : Tree (k + 1)) (μ : Tree k) (υ : list (Tree (k + 1))) : list ℕ :=
(derivative η μ υ).filter (λ i, @Tree'.is_sigma (k + 1) (μ↾*(i + 1)))

def lambda : Π (μ : Tree k) (υ : list (Tree (k + 1))), Tree (k + 1)
| []       _ := []
| (x :: μ) υ := let ih := lambda μ υ in
    option.cases_on (υ.nth μ.length) []
    (λ uμ, if uμ = ih ∨ (x.is_pi ∧ pi_derivative uμ μ υ = [])
    then (x :: μ) :: uμ else ih)

#check @Tree'.is_pi

def assignment (μ : Tree k) (υ : list (Tree (k + 1))) : Tree (k + 1) × ℕ :=
(S.priority (k + 1)).Min_le
  ((lambda μ υ, 0) :: ((list.range_r (lambda μ υ).length).filter
    (λ i, @Tree'.is_sigma (k + 2) (lambda μ υ↾*(i + 1)))).map
  (λ i, ((lambda μ υ)↾*i, (derivative (lambda μ υ↾*i) μ υ).length))) (by simp)

def up (μ : Tree k) (υ : list (Tree (k + 1))) : Tree (k + 1) :=
(assignment S μ υ).1

lemma ancestors_eq_range (μ : Tree k) : μ.ancestors.map ancestor.index = list.range_r μ.length :=
by { induction μ with ν μ IH; simp[ancestor.index, (∘)], exact IH }

lemma derivative_eq {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) (υ' : list (Tree (k + 1)))
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) (η : Tree (k + 1)) : 
  derivative η μ υ' = (approx.derivative η υ).map ancestor.index :=
by { simp[derivative, approx.derivative, ←ancestors_eq_range, list.map_filter, (∘)],
     congr, funext ν, simp [h] }

lemma pi_derivative_eq {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) (υ' : list (Tree (k + 1)))
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) (η : Tree (k + 1)) : 
  pi_derivative η μ υ' = (approx.pi_derivative η υ).map ancestor.index :=
by { simp[pi_derivative, approx.pi_derivative, derivative_eq _ _ h, list.map_filter, (∘)],
     congr, funext ν, simp[ancestor_initial_index_succ] }

lemma lambda_eq {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) (υ' : list (Tree (k + 1)))
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) : 
  lambda μ υ' = approx.lambda υ :=
begin
  induction μ with ν μ IH; simp[lambda, approx.lambda],
  rw [show υ'.nth μ.length = some (υ ⟨μ, by simp⟩), from h ⟨μ, by simp⟩], simp,
  have la_eq : lambda μ υ' = approx.lambda (ancestor.extend_fn υ μ _),
    from IH (ancestor.extend_fn υ μ (by simp)) (λ σ, h (σ.extend (by simp))),
  have pider_eq : ∀ η,
    pi_derivative η μ υ' = list.map ancestor.index (approx.pi_derivative η (ancestor.extend_fn υ μ _)),
    from pi_derivative_eq (ancestor.extend_fn υ μ (by simp)) υ'
    (λ σ, h (σ.extend (by simp))),
  simp[la_eq, pider_eq]
end

lemma assignment_eq {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) (υ' : list (Tree (k + 1)))
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) : 
  assignment S μ υ' = approx.assignment S υ :=
begin
  simp[assignment, approx.assignment, lambda_eq υ υ' h],
  refine omega_ordering.Min_le_eq _ _ _ _,
  simp,
  rw [←ancestors_eq_range],
  simp[list.map_filter, (∘)],
  congr,
  { funext ν, simp[ancestor_initial_index, derivative_eq _ _ h] },
  { ext ν, simp[ancestor_initial_index_succ] }
end

lemma up_eq {μ : Tree k} (υ : ancestor μ → Tree (k + 1)) (υ' : list (Tree (k + 1)))
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) : 
  up S μ υ' = approx.up S υ :=
congr_arg prod.fst (assignment_eq S υ υ' h)

lemma computable.derivative : computable
  (prod.unpaired3 (derivative : Tree (k + 1) → Tree k → list (Tree (k + 1)) → list ℕ)) :=
begin
  refine rcomputable.computable_of_rcomp (rcomputable.list_filter _ _),
  { refine (rcomputable₂.to_bool_eq (option (Tree (k + 1)))).comp₂ _ _,
    { exact rcomputable₂.list_nth.comp₂ (rcomputable.to_unary₁ rcomputable.snd.to_unary₂) rcomputable.id'.to_unary₂ },
    { exact rcomputable.to_unary₁ rcomputable.option_some.to_unary₁ } },
  { exact rcomputable.list_range_r.comp (rcomputable.list_length.comp rcomputable.fst.to_unary₂) }
end

lemma computable.pi_derivative : computable
  (prod.unpaired3 (pi_derivative : Tree (k + 1) → Tree k → list (Tree (k + 1)) → list ℕ)) :=
begin
  refine rcomputable.computable_of_rcomp (rcomputable.list_filter _ _),
  {  }
end

end approx_enc


lemma computable.is_pi {k} : computable (@Tree'.is_pi k) :=
begin
  induction k with k IH,
  { exact computable.id.of_eq (λ b, by cases b; simp) },
  { let F : Tree' (k + 1) → bool := λ μ, list.cases_on μ ff (λ η _, !@Tree'.is_pi k η),
    have : computable F,
    { refine rcomputable.computable_of_rcomp (rcomputable.list_rec (rcomputable.id') (rcomputable.const ff)
      ((rcomputable.dom_fintype bnot).comp (IH.to_rcomp.comp (rcomputable.fst.comp rcomputable.snd)))) },
    exact this.of_eq (λ μ, by { induction μ with ν μ IH; simp[F, Tree'.is_sigma] }) }
end

lemma computable.is_sigma {k} : computable (@Tree'.is_sigma k) :=
(primrec.dom_fintype bnot).to_comp.comp computable.is_pi

end strategy