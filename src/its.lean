import lib 

open encodable denumerable

attribute [simp] set.set_of_app_iff

def Tree' : ℕ → Type
| 0       := bool
| (n + 1) := list (Tree' n)

def Tree (n : ℕ) := Tree' (n + 1)

instance {k} : has_append (Tree k) := ⟨list.append⟩
instance {k} : has_mem (Tree' k) (Tree k) := ⟨list.mem⟩
instance : ∀ {k}, inhabited (Tree' k)
| 0       := ⟨tt⟩
| (k + 1) := ⟨[]⟩ 

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

def ancestor {n} (η : Tree n) := { μ : Tree n // μ ⊂ᵢ η }

instance {n} {η : Tree n} : has_coe (ancestor η) (Tree n) :=
⟨subtype.val⟩

instance {n} {η : Tree n} : linear_order (ancestor η) :=
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

def Tree.ancestors {n} (η : Tree n) : list (ancestor η) :=
(list.range_r η.length).pmap (λ m (h :m < η.length), (⟨η↾*m, list.is_initial_of_lt_length h⟩ : ancestor η))
(λ _, by simp)
-- η.ancestors = [ ... η↾*2, η↾*1, η↾*0]

def Tree.ancestors' {n} (η : Tree n) : list (Tree n) := η.ancestors.map subtype.val


namespace ancestor
variables {k : ℕ}

lemma le_iff {n} {η : Tree n} {μ₁ μ₂ : ancestor η} : μ₁ ≤ μ₂ ↔ μ₁.val <:+ μ₂.val := by refl

lemma lt_iff {n} {η : Tree n} {μ₁ μ₂ : ancestor η} : μ₁ < μ₂ ↔ μ₁.val ⊂ᵢ μ₂.val := by refl

def extend {η₁ η₂ : Tree k} (le : η₁ <:+ η₂) (μ : ancestor η₁) : ancestor η₂ :=
⟨μ, list.suffix_of_is_initial_is_initial μ.property le⟩

@[simp] lemma extend_val {η₁ η₂ : Tree k} (le : η₁ <:+ η₂) (μ : ancestor η₁) : 
  (μ.extend le).val = μ := rfl

def extend_fn {α} {η₂ : Tree k} 
  (f : ancestor η₂ → α) (η₁ : Tree k) (le : η₁ <:+ η₂) : ancestor η₁ → α := λ ν, f (ν.extend le)

@[simp] def extend_fn_val {α} {η₁ η₂ : Tree k}
  (f : ancestor η₂ → α) (le : η₁ <:+ η₂) (ν : ancestor η₁) : extend_fn f η₁ le ν = f (ν.extend le) := rfl

@[simp] lemma extend_id {n} {η : Tree n} {s} : @extend _ η η s = id :=
funext (by simp[extend])

@[simp] lemma ancestors_nil {n} : @Tree.ancestors n [] = [] := rfl

@[simp] lemma ancestors_cons {n} (η : Tree n) (x) :
  Tree.ancestors (x :: η) = ⟨η, by simp⟩ :: η.ancestors.map (extend (by simp)) :=
by { simp[Tree.ancestors, list.map_pmap], apply list.pmap_congr, simp,
     intros m eqn₁ eqn₂, simp [list.initial_cons eqn₂, extend] }

@[simp] lemma ancestors'_nil {n} : @Tree.ancestors' n [] = [] := rfl

@[simp] lemma ancestors'_cons {n} (η : Tree n) (x) :
  Tree.ancestors' (x :: η) = η :: η.ancestors' :=
by { simp [Tree.ancestors', ancestors_cons, function.comp], unfold_coes }


lemma ancestors_suffix_of_suffix {n} {μ₁ μ₂ : Tree n} (s : μ₁ <:+ μ₂) :
  μ₁.ancestors.map (ancestor.extend s) <:+ μ₂.ancestors :=
begin
  rcases s with ⟨l, h⟩,
  induction l with x l IH generalizing μ₁ μ₂,
  { simp at h, rcases h with rfl, simp },
  { simp at h, rcases h with rfl, simp,
    have : μ₁.ancestors.map (λ ν₁, (⟨ν₁.val, _⟩ : ancestor (x :: (l ++ μ₁))))
      <:+ list.map (extend (list.suffix_cons _ _)) (Tree.ancestors (l.append μ₁)),
    { have := list.map_suffix (extend (list.suffix_cons _ _)) (@IH μ₁ (l.append μ₁) rfl),
      simp[function.comp] at this, exact this },
    exact this.trans (list.suffix_cons _ _) }
end

@[simp] lemma ancestors_length {n} {μ : Tree n} : μ.ancestors.length = μ.length := by simp[Tree.ancestors]

lemma ancestors_rnth {n} {μ : Tree n} {i : ℕ} (h : i < μ.length)  :
  μ.ancestors.rnth i = some ⟨μ↾*i, list.is_initial_of_lt_length h⟩ :=
begin
  have : μ.ancestors.rnth i = μ.ancestors.nth (list.length μ - 1 - i),
  { have := @list.rnth_eq_nth_of_lt _ μ.ancestors i (by simp[h]), simp at this, exact this },
  rw this, simp[Tree.ancestors, list.nth_pmap],
  refine ⟨i, _, rfl⟩,
  have := @list.rnth_eq_nth_of_lt _ (list.range_r (list.length μ)) i (by simp[h]), simp[h] at this,
  exact eq.symm this
end

lemma ancestors_ordered {n} : ∀ (μ : Tree n), μ.ancestors.ordered (<)
| []       := by simp
| (x :: η) := by simp[list.ordered];
    exact ⟨list.ordered_map (extend (by simp)) (λ x y lt, lt) (ancestors_ordered η), λ η₀ mem, η₀.property⟩

lemma nodup_Tree.ancestors {n} (η : Tree n) : (Tree.ancestors η).nodup :=
list.nodup_pmap
  (λ m₁ eqn₁ m₂ eqn₂ eqn, by { simp at eqn, have : (η↾*m₁).length = m₁, from list.initial_length eqn₁,
       simp [eqn, list.initial_length eqn₂] at this, simp[this] })
  (list.nodup_range_r _)

def ancestor_univ {n} (η : Tree n) : finset (ancestor η) :=
⟨Tree.ancestors η, nodup_Tree.ancestors η⟩

@[simp] lemma ancestors_complete {n} {η : Tree n} (η₀ : ancestor η) : η₀ ∈ η.ancestors :=
list.mem_pmap.2 ⟨η₀.val.length, by { simp[ancestor_univ],
refine ⟨list.is_initial_length η₀.property, _⟩, apply subtype.ext, simp,
exact list.eq_initial_of_is_initial η₀.property }⟩

@[simp] lemma mem_fin_range {n} {η : Tree n} (η₀ : ancestor η) : η₀ ∈ ancestor_univ η :=
ancestors_complete _

instance {n} (η : Tree n) : fintype (ancestor η) :=
⟨ancestor_univ η, mem_fin_range⟩

def ancestor_univ' {n} (η : Tree n) : finset (Tree n) := (ancestor_univ η).image subtype.val  

@[simp] lemma ancestor_univ_card {n} (η : Tree n) : (ancestor_univ η).card = η.length :=
by simp[ancestor_univ, Tree.ancestors]

@[simp] lemma ancestor_univ'_card {n} (η : Tree n) : (ancestor_univ' η).card = η.length :=
by { have : (ancestor_univ' η).card = (ancestor_univ η).card,
     { apply finset.card_image_of_injective, intros x y, exact subtype.eq },
     simp[this] }

end ancestor

def out {n} : Π {η : Tree n}, ancestor η → Tree' n
| []       ⟨μ, μ_p⟩ := by exfalso; simp* at*
| (ν :: η) ⟨μ, μ_p⟩ := if h : μ ⊂ᵢ η then out ⟨μ, h⟩ else ν

lemma out_eq_iff {n} : ∀ {η : Tree n} {μ : ancestor η} {ν}, out μ = ν ↔ ν :: μ.val <:+ η
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

lemma out_eq_iff' {n} {η : Tree n} {μ : ancestor η} {ν} : ν = out μ ↔ ν :: μ.val <:+ η :=
by { rw[←out_eq_iff], exact eq_comm }

lemma suffix_out_cons {n} {η : Tree n} (μ : ancestor η) : out μ :: μ.val <:+ η :=
by { have := @out_eq_iff n η μ (out μ), simp* at* }

lemma out_cons'_eq {n} {η : Tree n} (ν) (μ : ancestor η)  :
  @out n (ν :: η) (μ.extend (list.suffix_cons ν η)) = out μ :=
by { simp[out, ancestor.extend], intros h, exfalso, have := h μ.property, exact this }

lemma out_cons'_eq' {n} {η : Tree n} (ν) (μ : ancestor η) {h : μ.val ⊂ᵢ ν :: η} :
  @out n (ν :: η) ⟨μ.val, h⟩ = out μ :=
by { simp[out], intros h, exfalso, have := h μ.property, exact this }

lemma suffix_out_eq {n} : ∀ {η₁ η₂: Tree n} {μ₁ : ancestor η₁} {μ₂ : ancestor η₂}
  (h₁ : μ₁.val = μ₂.val) (h₂ : η₂ <:+ η₁), out μ₁ = out μ₂ :=
begin
  suffices : ∀ (l : list _) {η₁ η₂: Tree n} {μ₁ : ancestor η₁} {μ₂ : ancestor η₂}
    (h₁ : μ₁.val = μ₂.val) (h₂ : l.reverse ++ η₂ = η₁), out μ₁ = out μ₂,
  { intros η₁ η₂ μ₁ μ₂ h₁ h₂, rcases h₂ with ⟨l, h₂⟩,
    exact this l.reverse h₁ (by simp[h₂]) },
  intros l η₁ η₂ μ₁ μ₂ h₁ h₂,
  induction l with ν l IH generalizing η₁ η₂,
  { simp at h₂, rcases h₂ with rfl, congr, exact subtype.eq h₁ },
  { simp at h₂,
    let μ₂' : ancestor (ν :: η₂) := ⟨μ₂.val, μ₂.property.trans (by simp)⟩,
    have h₁' : μ₁.val = μ₂'.val, { simp[μ₂', h₁] },
    have eqn₁ : out μ₁ = out μ₂', from IH h₁' h₂,
    have eqn₂ : out μ₂' = out μ₂, from out_cons'_eq' ν μ₂,
    simp[eqn₁, eqn₂] }
end

@[simp] lemma out_extend_eq {k} {η₁ η₂ : Tree k} {h : η₁ <:+ η₂} {μ₁ : ancestor η₁} :
  out (ancestor.extend h μ₁) = out μ₁ :=
suffix_out_eq (by simp) h

@[simp] lemma out_cons {k} {η : Tree k} {x} (h : η ⊂ᵢ x :: η) : out ⟨η, h⟩ = x := by simp[out_eq_iff]

@[simp] def Tree'.is_pie : Π {k} (η : Tree' k), bool
| 0       ff       := ff
| 0       tt       := tt
| (k + 1) (η :: _) := !Tree'.is_pie η
| (k + 1) []       := ff

def Tree'.is_sigma {k} (η : Tree' k) : bool := !η.is_pie

@[simp] def Tree'.is_validated : Π {k} (η : Tree' k), bool
| 0       ff       := ff
| 0       tt       := tt
| (k + 1) (η :: _) := Tree'.is_validated η
| (k + 1) []       := ff

@[simp] lemma is_pie_neg {k} {η : Tree k} : !η.is_pie ↔ η.is_sigma := by simp[Tree'.is_sigma]
lemma neg_is_pie_iff {k} {η : Tree k} : ¬η.is_pie ↔ η.is_sigma :=
by { unfold Tree'.is_sigma, cases Tree'.is_pie η; simp }
@[simp] lemma is_pie_eq_ff {k} {η : Tree' k} : η.is_pie = ff ↔ η.is_sigma :=
by { unfold Tree'.is_sigma, cases Tree'.is_pie η; simp }

def ancestor.pie_outcome {k} {η : Tree k} (μ : ancestor η) : bool := (out μ).is_sigma
def ancestor.sigma_outcome {k} {η : Tree k} (μ : ancestor η) : bool := (out μ).is_pie

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

lemma eq_out_of_sigma {μ₁ μ₂ : Tree k} (le : μ₁ <:+ μ₂)
  (η : Tree (k + 1)) (lt₁ : η ⊂ᵢ S.lambda μ₁) (lt₂ : η ⊂ᵢ S.lambda μ₂) (sigma : (out ⟨η, lt₁⟩).is_sigma) :
  out ⟨η, lt₁⟩ = out ⟨η, lt₂⟩ :=
begin
  have lmm₁ : out ⟨η, lt₁⟩ :: η <:+ S.lambda μ₂, from S.sigma_preserve le sigma lt₂,
  have lmm₂ : out ⟨η, lt₂⟩ :: η <:+ S.lambda μ₂, from suffix_out_cons ⟨η, lt₂⟩,
  have := list.suffix_of_suffix_length_le lmm₁ lmm₂ (by simp), simp at this, exact this
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



end strategy


