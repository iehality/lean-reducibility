import its reducibility

open encodable denumerable

attribute [simp] set.set_of_app_iff

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]
  {o : σ →. τ}
variables {n : ℕ} (S : strategy n) {k : ℕ}

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

@[rcomputability]
lemma rcomputable.is_pi {k} : @Tree'.is_pi k computable_in o :=
begin
  induction k with k IH,
  { exact rcomputable.id.of_eq (λ b, by cases b; simp) },
  { let F : Tree' (k + 1) → bool := λ μ, list.cases_on μ ff (λ η _, !@Tree'.is_pi k η),
    have : F computable_in o,
    { refine (rcomputable.list_rec (rcomputable.id') (rcomputable.const ff)
      ((rcomputable.dom_fintype bnot).comp (IH.comp (rcomputable.fst.comp rcomputable.snd)))) },
    exact this.of_eq (λ μ, by { induction μ with ν μ IH; simp[F, Tree'.is_sigma] }) }
end

@[rcomputability]
lemma rcomputable.is_sigma {k} : @Tree'.is_sigma k computable_in o :=
(rcomputable.dom_fintype bnot).comp rcomputable.is_pi

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

def assignment (μ : Tree k) (υ : list (Tree (k + 1))) : Tree (k + 1) × ℕ :=
(S.priority (k + 1)).Min_le
  ((lambda μ υ, 0) :: ((list.range_r (lambda μ υ).length).filter
    (λ i, @Tree'.is_sigma (k + 2) (lambda μ υ↾*(i + 1)))).map
  (λ i, ((lambda μ υ)↾*i, (derivative (lambda μ υ↾*i) μ υ).length))) (by simp)

def up (μ : Tree k) (υ : list (Tree (k + 1))) : Tree (k + 1) :=
(assignment S μ υ).1

lemma ancestors_eq_range (μ : Tree k) : μ.ancestors.map ancestor.index = list.range_r μ.length :=
by { induction μ with ν μ IH; simp[ancestor.index, (∘)], exact IH }

lemma derivative_eq {μ : Tree k} {υ : ancestor μ → Tree (k + 1)} {υ' : list (Tree (k + 1))}
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) (η : Tree (k + 1)) : 
  derivative η μ υ' = (approx.derivative η υ).map ancestor.index :=
by { simp[derivative, approx.derivative, ←ancestors_eq_range, list.map_filter, (∘)],
     congr, funext ν, simp [h] }

lemma pi_derivative_eq {μ : Tree k} {υ : ancestor μ → Tree (k + 1)} {υ' : list (Tree (k + 1))}
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) (η : Tree (k + 1)) : 
  pi_derivative η μ υ' = (approx.pi_derivative η υ).map ancestor.index :=
by { simp[pi_derivative, approx.pi_derivative, derivative_eq h, list.map_filter, (∘)],
     congr, funext ν, simp[ancestor_initial_index_succ] }

lemma lambda_eq {μ : Tree k} {υ : ancestor μ → Tree (k + 1)} {υ' : list (Tree (k + 1))}
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) : 
  lambda μ υ' = approx.lambda υ :=
begin
  induction μ with ν μ IH; simp[lambda, approx.lambda],
  rw [show υ'.nth μ.length = some (υ ⟨μ, by simp⟩), from h ⟨μ, by simp⟩], simp,
  have la_eq : lambda μ υ' = approx.lambda (ancestor.extend_fn υ μ _),
    from @IH (ancestor.extend_fn υ μ (by simp)) (λ σ, h (σ.extend (by simp))),
  have pider_eq : ∀ η,
    pi_derivative η μ υ' = list.map ancestor.index (approx.pi_derivative η (ancestor.extend_fn υ μ _)),
    from @pi_derivative_eq _ _ (ancestor.extend_fn υ μ (by simp)) υ'
    (λ σ, h (σ.extend (by simp))),
  simp[la_eq, pider_eq]
end

lemma assignment_eq {μ : Tree k} {υ : ancestor μ → Tree (k + 1)} {υ' : list (Tree (k + 1))}
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) : 
  assignment S μ υ' = approx.assignment S υ :=
begin
  simp[assignment, approx.assignment, lambda_eq h],
  refine omega_ordering.Min_le_eq _ _ _ _,
  simp,
  rw [←ancestors_eq_range],
  simp[list.map_filter, (∘)],
  congr,
  { funext ν, simp[ancestor_initial_index, derivative_eq h] },
  { ext ν, simp[ancestor_initial_index_succ] }
end

lemma up_eq {μ : Tree k} {υ : ancestor μ → Tree (k + 1)} {υ' : list (Tree (k + 1))}
  (h : ∀ ν : ancestor μ, υ'.nth ν.index = some (υ ν)) : 
  up S μ υ' = approx.up S υ :=
congr_arg prod.fst (assignment_eq S h)

variables {S}
open rcomputable computable₂

lemma rcomputable.derivative :
  (prod.unpaired3 (derivative : Tree (k + 1) → Tree k → list (Tree (k + 1)) → list ℕ)) computable_in o :=
begin
  refine rcomputable.list_filter _ _,
  { refine (rcomputable₂.to_bool_eq (option (Tree (k + 1)))).comp₂ _ _,
    { exact rcomputable₂.list_nth.comp₂ (rcomputable.to_unary₁ rcomputable.snd.to_unary₂) rcomputable.id'.to_unary₂ },
    { exact rcomputable.to_unary₁ rcomputable.option_some.to_unary₁ } },
  { exact rcomputable.list_range_r.comp (rcomputable.list_length.comp rcomputable.fst.to_unary₂) }
end

lemma rcomputable.pi_derivative : 
  (prod.unpaired3 (pi_derivative : Tree (k + 1) → Tree k → list (Tree (k + 1)) → list ℕ)) computable_in o :=
begin
  refine rcomputable.list_filter _ rcomputable.derivative,
  { simp, exact rcomputable.is_sigma.comp₂
    (rcomputable.rcomputable.list_initial.comp₂ (rcomputable.to_unary₁ rcomputable.fst.to_unary₂)
    rcomputable.succ.to_unary₂) }
end

lemma rcomputable.lambda : 
  (lambda : Tree k → list (Tree (k + 1)) → Tree (k + 1)) computable₂_in o :=
begin
  let F : Tree k → list (Tree (k + 1)) → Tree (k + 1) :=
    λ μ υ, list.rec_on μ []
      (λ x μ ih, option.cases_on (υ.nth μ.length) []
        (λ uμ, if uμ = ih ∨ (x.is_pi ∧ pi_derivative uμ μ υ = []) then (x :: μ) :: uμ else ih)),
  have : F computable₂_in o,
  { simp[F],
    refine rcomputable.list_rec (rpartrec.some.to_unary₁) (rcomputable.const list.nil)
      (rcomputable.option_rec
        (rcomputable₂.list_nth.comp snd.to_unary₁
          (rcomputable.list_length.comp (fst.comp snd.to_unary₂)))
        (rcomputable.const list.nil)
      (rcomputable.ite _ _ _)),
    { simp, refine rcomputable.bor.comp _
        (rcomputable.band.comp (rcomputable.is_pi.comp (fst.comp snd.to_unary₁)) _),
      { refine (rcomputable₂.to_bool_eq _).comp snd
        (snd.comp (snd.comp snd.to_unary₁)) },
      { refine (rcomputable₂.to_bool_eq _).comp
          (rcomputable.pi_derivative.unpaired3 snd
            (fst.comp (snd.comp snd.to_unary₁))
            (snd.comp fst.to_unary₁)) (rcomputable.const []) } },
    { exact rcomputable₂.list_cons.comp
        (rcomputable₂.list_cons.comp (fst.comp snd.to_unary₁)
        (fst.comp (snd.comp snd.to_unary₁)))
        snd },
    { exact snd.comp (snd.comp snd.to_unary₁) } },
  exact this.of_eq (λ μ υ, by {
    induction μ with x μ IH; simp[F, lambda],
    { cases C : υ.nth μ.length with ν; simp[C],
      { simp[F, lambda] at IH, simp[IH] } } })
end

lemma rcomputable.assignment_enc : 
  (assignment S : Tree k → list (Tree (k + 1)) → Tree (k + 1) × ℕ) computable₂_in o :=
(omega_ordering_Min_le (S.priority (k + 1)) _ _ (S.effective _).to_rcomp
  (rcomputable₂.list_cons.comp (pair (rcomputable.lambda.comp fst snd) (const 0))
    (list_map
      (pair (rcomputable.list_initial.comp (rcomputable.lambda.comp fst.to_unary₁ snd.to_unary₁) snd)
        (list_length.comp (rcomputable.derivative.unpaired3
          (rcomputable.list_initial.comp (rcomputable.lambda.comp fst.to_unary₁ snd.to_unary₁) snd)
          (fst.to_unary₁) (snd.to_unary₁))))
      (list_filter
        (by {simp, exact is_sigma.comp₂ 
          (rcomputable.list_initial.comp₂ (rcomputable.lambda.comp fst snd).to_unary₁ succ.to_unary₂) })
        (list_range_r.comp (list_length.comp (rcomputable.lambda.comp fst snd)))))))

lemma rcomputable.up_enc : 
  (up S : Tree k → list (Tree (k + 1)) → Tree (k + 1)) computable₂_in o :=
fst.comp rcomputable.assignment_enc

end approx_enc

def up'_enc : Tree k → list (Tree (k + 1))
| []       := []
| (_ :: η) := up'_enc η ++ [approx_enc.up S η (up'_enc η)]

@[simp] lemma up'_enc_length (μ : Tree k) : (up'_enc S μ).length = μ.length :=
by induction μ with ν μ IH; simp[up'_enc]; exact IH

variables {S}
open rcomputable rcomputable₂

lemma rcomputable.up'_enc : (up'_enc S : Tree k → list (Tree (k + 1))) computable_in o :=
begin
  let F : Tree k → list (Tree (k + 1)) := λ μ, list.rec_on μ [] (λ _ η IH, IH ++ [approx_enc.up S η IH]),
  have : F computable_in o,
  { simp[F],
    refine rcomputable.list_rec rcomputable.id' (const []) _,
    exact list_append.comp (snd.comp snd.to_unary₂)
      (list_cons.comp (approx_enc.rcomputable.up_enc.comp (fst.comp snd.to_unary₂) (snd.comp snd.to_unary₂))
      (const [])) },
  exact this.of_eq (λ μ, by { 
    induction μ with ν μ IH; simp[F, up'_enc],
    { simp[F] at IH, simp[IH] }  })
end

lemma up_enc_eq_up {μ : Tree k} : ∀ ν : ancestor μ, (S.up'_enc μ).nth ν.index = some (S.up' μ ν) :=
begin
  induction μ with ν μ IH; simp[up'_enc, up' S, -up'_up_consistent],
    {  rintros ⟨σ, lt⟩,simp at lt, contradiction },
    { rintros ⟨σ, lt⟩, simp[up', -up'_up_consistent],
      have : σ = μ ∨ σ ⊂ᵢ μ, from list.is_initial_cons_iff.mp lt,
      rcases this with (rfl | lt),
      { simp[ancestor.index],
        rw [show σ.length = (S.up'_enc σ).length, by simp, list.nth_concat_length],
        simp, refine approx_enc.up_eq S IH },
      { simp[lt, ancestor.index],
        rw [list.nth_append (show list.length σ < (S.up'_enc μ).length, by simp[list.is_initial_length lt])],
        have := IH ⟨σ, lt⟩, simp[ancestor.index] at this, exact this } }
end

@[rcomputability]
theorem rcomputable.up : (up[S] : Tree k → Tree (k + 1)) computable_in o :=
(approx_enc.rcomputable.up_enc.comp id' rcomputable.up'_enc).of_eq
(λ μ, approx_enc.up_eq S up_enc_eq_up)


@[rcomputability]
theorem rcomputable.lambda : (λ[S] : Tree k → Tree (k + 1)) computable_in o :=
by { have : (λ μ : Tree k, approx_enc.lambda μ (S.up'_enc μ)) computable_in o,
       from approx_enc.rcomputable.lambda.comp id' rcomputable.up'_enc,
     exact this.of_eq (λ μ, approx_enc.lambda_eq up_enc_eq_up) }

lemma rcomputable.Tree'_weight_aux {k : ℕ} :
  (Tree'.weight_aux : Tree' k → ℕ) computable_in o :=
begin
  induction k with k IH,
  { exact (id'.cond (const 1) (const 0)).of_eq (λ μ, by cases μ; simp[Tree'.weight_aux]) },
  { exact list_weight_of IH }
end

@[rcomputability]
lemma rcomputable.Tree_weight {k : ℕ} :
  (Tree.weight : Tree k → ℕ) computable_in o :=
begin
  induction k with k IH,
  { exact rcomputable.Tree'_weight_aux },
  { let F : Tree (k + 1) → ℕ := λ μ, list.rec_on μ 0 (λ ν _ _, ν.weight_aux + 1),
    have : F computable_in o,
    { simp[F], refine rcomputable.list_rec id (const 0)
      (nat_add.comp (rcomputable.Tree'_weight_aux.comp fst.to_unary₂) (const 1)) },
    exact this.of_eq (λ μ, by cases μ; simp[F, Tree.weight]) }
end

end strategy