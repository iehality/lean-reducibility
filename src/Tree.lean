import lib 

open encodable denumerable

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

instance : has_zero (zero ⊕ infinity) := ⟨sum.inl zero.zero⟩

notation `∞` := sum.inl infinity.infinity

instance {n} : has_ssubset (Tree n) := ⟨λ x y, x ⊂ᵢ y⟩
instance {n} : has_subset (Tree n) := ⟨λ x y, x <:+ y⟩

def ancestor {n} (η : Tree n) := { μ : Tree n // μ ⊂ᵢ η }

instance {n} {η : Tree n} : linear_order (ancestor η) :=
{ le := λ x y, x.val <:+ y.val,
  lt := λ x y, x.val ⊂ᵢ y.val,
  le_refl := λ μ, by simp,
  le_trans := λ μ₁ μ₂ μ₃, list.is_suffix.trans,
  lt_iff_le_not_le := λ μ₁ μ₂, by { simp[list.is_initial_iff_suffix], intros h₁,
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

namespace ancestor

instance {n} {η : Tree n} : has_coe (ancestor η) (Tree n) :=
⟨subtype.val⟩

lemma le_iff {n} {η : Tree n} {μ₁ μ₂ : ancestor η} : μ₁ ≤ μ₂ ↔ μ₁.val ⊆ μ₂.val := by refl

lemma lt_iff {n} {η : Tree n} {μ₁ μ₂ : ancestor η} : μ₁ < μ₂ ↔ μ₁.val ⊂ μ₂.val := by refl

@[simp] def extend {n} {η₁ η₂ : Tree n} (s : η₁ <:+ η₂) (μ : ancestor η₁) : ancestor η₂ :=
⟨μ.val, list.suffix_of_is_initial_is_initial μ.property s⟩

@[simp] lemma extend_id {n} {η : Tree n} {s} : @extend _ η η s = id :=
funext (by simp)

@[simp] lemma ancestors_nil {n} : @Tree.ancestors n [] = [] := rfl

@[simp] lemma ancestors_cons {n} (η : Tree n) (x) :
  Tree.ancestors (x :: η) = ⟨η, by simp⟩ :: η.ancestors.map (extend (by simp)) :=
by { simp[Tree.ancestors, list.map_pmap], apply list.pmap_congr, simp,
     intros m eqn₁ eqn₂, simp [list.initial_cons eqn₂, extend] }

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

structure Path (n : ℕ) :=
(path : ℕ → Tree n)
(mono : ∀ m, path m <:+ path (m + 1))

namespace Path

def trivialPath_aux {i : ℕ} : ℕ → Tree i
| 0       := []
| (n + 1) := ∞ :: trivialPath_aux n

instance (i) : nonempty (Path i) := ⟨⟨trivialPath_aux, by simp[trivialPath_aux]⟩⟩

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

lemma ssubset_of_le {n m : ℕ} {η : Tree i} (ss : η ⊂ Λ.path n) (le : n ≤ m) : η ⊂ Λ.path m :=
list.suffix_of_is_initial_is_initial ss (Λ.mono' le)

def ssubset {i} (η : Tree i) (Λ : Path i) : Prop := ∃ n, η ⊂ Λ.path n
def subset {i} (η : Tree i) (Λ : Path i): Prop := ∃ n, η ⊆ Λ.path n

infix ` ⊂' `:50   := Path.ssubset
infix ` ⊆' `:50   := Path.subset



end Path

def out {n} : Π {η : Tree n}, ancestor η → infinity ⊕ Tree' n
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

lemma rnth_eq_iff_out {n} {η : Tree n} {ν} {m : ℕ} :
  η.rnth m = some ν ↔ ν :: η↾*m <:+ η :=
list.rnth_eq_iff_suffix_cons_initial

lemma rnth_eq_some_out {n} {η : Tree n} {μ : ancestor η} {m : ℕ} (h : m < η.length) :
  η.rnth m = some (out (⟨η↾*m, list.is_initial_of_lt_length h⟩ : ancestor η)) :=
rnth_eq_iff_out.mpr (suffix_out_cons ⟨η↾*m, list.is_initial_of_lt_length h⟩)


