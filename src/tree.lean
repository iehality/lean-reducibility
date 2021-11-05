import lib 

open encodable denumerable

attribute [simp] set.set_of_app_iff

def Tree' : ℕ → Type
| 0       := bool
| (n + 1) := list (Tree' n)

def Tree (n : ℕ) := Tree' (n + 1)

instance {k} : has_append (Tree k) := ⟨list.append⟩
instance {k} : has_mem (Tree' k) (Tree k) := ⟨list.mem⟩
instance {k} : has_mem (Tree' k) (Tree' (k + 1)) := ⟨list.mem⟩
instance : ∀ {k}, inhabited (Tree' k)
| 0       := ⟨tt⟩
| (k + 1) := ⟨[]⟩ 

instance : ∀ n, decidable_eq (Tree' n)
| 0       := bool.decidable_eq
| (n + 1) := @list.decidable_eq _ (Tree'.decidable_eq n)

instance : ∀ n, primcodable (Tree' n)
| 0       := primcodable.bool
| (s + 1) := @primcodable.list (Tree' s) (Tree'.primcodable s)

instance (n) : primcodable (Tree n) := Tree'.primcodable (n + 1)

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

def Tree.ancestors' {n} (η : Tree n) : Tree (n + 1) := η.ancestors.map subtype.val

def Tree.ancestors_or_refl {n} (η : Tree n) : Tree (n + 1) := η :: η.ancestors'

namespace ancestor
variables {k : ℕ}

lemma le_iff {n} {η : Tree n} {μ₁ μ₂ : ancestor η} : μ₁ ≤ μ₂ ↔ μ₁.val <:+ μ₂.val := by refl

lemma lt_iff {n} {η : Tree n} {μ₁ μ₂ : ancestor η} : μ₁ < μ₂ ↔ μ₁.val ⊂ᵢ μ₂.val := by refl

@[simp] def mk' {k} {η μ : Tree k} (h : μ ⊂ᵢ η) : ancestor η := ⟨μ, h⟩

def extend {η₁ η₂ : Tree k} (le : η₁ <:+ η₂) (μ : ancestor η₁) : ancestor η₂ :=
⟨μ, list.is_initial.is_initial_of_suffix μ.property le⟩

@[simp] lemma extend_val {η₁ η₂ : Tree k} (le : η₁ <:+ η₂) (μ : ancestor η₁) : 
  (μ.extend le).val = μ := rfl

@[simp] lemma extend_coe {η₁ η₂ : Tree k} (le : η₁ <:+ η₂) (μ : ancestor η₁) : 
  (↑(μ.extend le) : Tree k) = ↑μ := rfl

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

lemma ancestors'_suffix_of_suffix {n} {μ₁ μ₂ : Tree n} (s : μ₁ <:+ μ₂) :
  μ₁.ancestors' <:+ μ₂.ancestors' :=
begin
  rcases s with ⟨l, rfl⟩,
  induction l with x l IH,
  { refl },
  { simp, exact IH.trans (list.suffix_cons _ _) }
end

lemma ancestors_suffix_of_suffix' {n} {μ₁ μ₂ : Tree n} (s : μ₁ <:+ μ₂) :
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

@[simp] lemma ancestors_or_reflngth {n} {μ : Tree n} : μ.ancestors.length = μ.length := by simp[Tree.ancestors]

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

lemma ancestors'_complete {n} {η : Tree n} (η₀ : Tree n) (lt : η₀ ⊂ᵢ η) : η₀ ∈ η.ancestors' :=
by { simp[Tree.ancestors'], refine ⟨⟨η₀, lt⟩, rfl⟩ }

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


structure Path (n : ℕ) :=
(path : ℕ → Tree n)
(mono : ∀ m, path m <:+ path (m + 1))

instance {n : ℕ} : has_coe_to_fun (Path n) (λ _, ℕ → Tree n) := ⟨Path.path⟩

namespace Path

lemma ext {k} {Λ₁ Λ₂ : Path k} (h : ∀ s, Λ₁ s = Λ₂ s) : Λ₁ = Λ₂ :=
by { rcases Λ₁ with ⟨P₁, _⟩, rcases Λ₂ with ⟨P₂, _⟩, simp,
     refine funext h }

@[simp] lemma path_eta {n : ℕ} {p : ℕ → Tree n} {h} : (({path := p, mono := h} : Path n) : ℕ → Tree n) = p := rfl

def trivialPath_aux {i : ℕ} : ℕ → Tree i
| 0       := []
| (n + 1) := (default _) :: trivialPath_aux n

instance (i) : inhabited (Path i) := ⟨⟨trivialPath_aux, by simp[trivialPath_aux]⟩⟩

variables {k : ℕ} (Λ : Path k)

lemma mono' : ∀ {n m : ℕ} (le : n ≤ m), Λ n <:+ Λ m :=
begin
  suffices : ∀ n m, Λ n <:+ Λ (n + m),
  { intros n m eqn, have := this n (m - n), simp[nat.add_sub_of_le eqn] at this,
    exact this },
  intros n m, induction m with m IH,
  { refl },
  { simp[←nat.add_one, ←add_assoc], exact IH.trans (Λ.mono _) }
end

lemma ssubset_of_le {n m : ℕ} {η : Tree k} (ss : η ⊂ᵢ Λ n) (le : n ≤ m) : η ⊂ᵢ Λ m :=
list.is_initial.is_initial_of_suffix ss (Λ.mono' le)

def ssubset (η : Tree k) (Λ : Path k) : Prop := ∃ n, η ⊂ᵢ Λ n
def subset (η : Tree k) (Λ : Path k): Prop := ∃ n, η <:+ Λ n

infix ` ⊂' `:50   := Path.ssubset
infix ` ⊆' `:50   := Path.subset

def infinite (Λ : Path k) : Prop := ∀ n, ∃ m, Λ n ⊂ᵢ Λ (n + m)

def thick (Λ : Path k) : Prop := Λ 0 = [] ∧ ∀ n, ∃ ν, Λ (n + 1) = ν :: Λ n

def le (Λ₁ Λ₂ : Path k) : Prop := ∀ n, ∃ m, Λ₁ n <:+ Λ₂ m
infix ` ≤ₚ `:80 := le

def equiv (Λ₁ Λ₂ : Path k) : Prop := Λ₁.le Λ₂ ∧ Λ₂.le Λ₁
infix ` ≃ₚ `:80 := equiv

@[refl] lemma equiv.refl (Λ : Path k) : Λ ≃ₚ Λ :=
⟨λ n, ⟨n, by refl⟩, λ n, ⟨n, by refl⟩⟩

@[symm] lemma equiv.symm {Λ₁ Λ₂ : Path k} : Λ₁ ≃ₚ Λ₂ → Λ₂ ≃ₚ Λ₁ := and.symm

@[trans] lemma equiv.trans {Λ₁ Λ₂ Λ₃ : Path k} (eqn₁ : Λ₁ ≃ₚ Λ₂) (eqn₂ : Λ₂ ≃ₚ Λ₃) : Λ₁ ≃ₚ Λ₃ :=
⟨λ n, by { rcases eqn₁.1 n with ⟨m, le₁⟩, rcases eqn₂.1 m with ⟨l, le₂⟩, refine ⟨l, le₁.trans le₂⟩ },
 λ n, by { rcases eqn₂.2 n with ⟨m, le₁⟩, rcases eqn₁.2 m with ⟨l, le₂⟩, refine ⟨l, le₁.trans le₂⟩ }⟩

lemma le.ssubset_of_ssubset {Λ₁ Λ₂ : Path k} (eqn : Λ₁ ≤ₚ Λ₂) {μ} (lt : μ ⊂' Λ₁) : μ ⊂' Λ₂ :=
by { rcases lt with ⟨n, lt⟩,
     rcases eqn n with ⟨m, eqn⟩, refine ⟨m, _⟩, exact list.is_initial.is_initial_of_suffix lt eqn }

lemma infinite.length {Λ : Path k} (h : Λ.infinite) (n : ℕ) : ∃ m, n < (Λ m).length :=
begin
  induction n with n IH,
  { rcases h 0 with ⟨m, h⟩, simp at h,
    refine ⟨m, _⟩, cases Λ m; simp at*, { contradiction } },
  { rcases IH with ⟨m, IH⟩, rcases h m with ⟨m', h⟩, refine ⟨m + m', _⟩,
    exact gt_of_gt_of_ge (h.lt_length) IH }
end

lemma thick.infinite {Λ : Path k} (h : Λ.thick) : Λ.infinite :=
λ s, ⟨1, by { rcases h.2 s with ⟨ν, eqn⟩, simp[eqn] }⟩

lemma thick.is_initial_of_lt {Λ : Path k} (h : Λ.thick) {s t : ℕ} (lt : s < t) : Λ s ⊂ᵢ Λ t :=
by { have : Λ s ⊂ᵢ Λ (s + 1), { rcases h.2 s with ⟨ν, eqn⟩, simp[eqn] },
     exact list.is_initial.is_initial_of_suffix this (Λ.mono' (nat.succ_le_iff.mpr lt)) }

lemma thick.length {Λ : Path k} (h : Λ.thick) (s : ℕ) : (Λ s).length = s :=
by { induction s with s IH, { simp[h.1] }, { rcases h.2 s with ⟨ν, eqn⟩, simp[eqn, IH] } }

lemma thick.ssubset {Λ : Path k} (h : Λ.thick) {μ} : μ ⊆' Λ ↔ ∃ s, μ = Λ s :=
⟨λ ss, by { rcases ss with ⟨s, eqn⟩, refine ⟨μ.length, _⟩,
     have : μ.length ≤ s,
     { have := eqn.le_length, simp[h.length] at this, exact this },
     have := list.suffix_of_suffix_length_le eqn (Λ.mono' this) (by simp[h.length]),
     exact list.eq_of_suffix_of_length_eq this (by simp[h.length]) }, λ ⟨s, eqn⟩, ⟨s, by simp[eqn]⟩⟩

lemma thick.eq_length_of_le {Λ : Path k} (h : Λ.thick) (μ : Tree k) (le : μ ⊆' Λ) : (Λ μ.length) = μ :=
by { rcases h.ssubset.mp le with ⟨s, rfl⟩, simp[h.length] }

lemma thick.lt_mono_iff {Λ : Path k} (h : Λ.thick) {s t : ℕ} : Λ s ⊂ᵢ Λ t ↔ s < t :=
by { have : s < t ∨ t ≤ s, from lt_or_ge s t, rcases this with (lt | le),
     { simp[lt], exact thick.is_initial_of_lt h lt },
     { simp[not_lt.mpr le], intros lt, exact list.is_initial_suffix_antisymm lt (Λ.mono' le) } }

lemma thick.le_mono_iff {Λ : Path k} (h : Λ.thick) {n m : ℕ} : Λ n <:+ Λ m ↔ n ≤ m :=
begin
  have C : n < m ∨ n = m ∨ m < n, from trichotomous n m,
  cases C,
  { have := h.is_initial_of_lt C, simp[le_of_lt C], exact list.is_initial.suffix this }, rcases C with (rfl | C),
  { simp },
  { simp[not_le.mpr C], have := h.is_initial_of_lt C, exact list.is_initial_suffix_antisymm this }
end

lemma thick.out {Λ : Path k} (h : Λ.thick) (s : ℕ) : Tree' k := out (⟨Λ s, h.is_initial_of_lt (lt_add_one s)⟩)

lemma infinite.thick_exists {Λ : Path k} (h : Λ.infinite) :
  ∃ Λ' : Path k, Λ' ≃ₚ Λ ∧ Λ'.thick :=
begin
  have : ∃ f : ℕ → ℕ, ∀ x, x < list.length (Λ (f x)), from classical.skolem.mp (infinite.length h),
  rcases this with ⟨f, eqn⟩,
  let P : ℕ → Tree k := λ s, Λ (f s)↾*s,
  have P_length : ∀ s, (P s).length = s, from λ s, list.initial_length (eqn s),
  have le : ∀ s, P s <:+ P (s + 1),
  { intros s, simp[P],
    have lmm₁ : P s <:+ Λ (max (f s) (f (s + 1))),
      from (list.suffix_initial (Λ (f s)) s).trans (Λ.mono' (le_max_left _ _)),
    have lmm₂ : P (s + 1) <:+ Λ (max (f s) (f (s + 1))),
      from (list.suffix_initial (Λ (f (s + 1))) (s + 1)).trans (Λ.mono' (le_max_right _ _)),  
    refine list.suffix_of_suffix_length_le lmm₁ lmm₂ (by simp[P_length]) },
  let Λ' : Path k := ⟨P, le⟩,
  have equiv : Λ' ≃ₚ Λ,
  { split, { intros s, exact ⟨f s, list.suffix_initial _ _⟩ },
    { intros s, refine ⟨(Λ s).length, _⟩, simp[Λ', P],
      have lmm₁ : Λ s <:+ Λ (max s (f (Λ s).length)), from Λ.mono' (le_max_left _ _),
      have lmm₂ : P (Λ s).length <:+ Λ (max s (f (Λ s).length)),
        from (list.suffix_initial (Λ (f _)) _).trans (Λ.mono' (le_max_right _ _)),
      refine list.suffix_of_suffix_length_le lmm₁ lmm₂ (by simp[P_length]) } },
  have thick : Λ'.thick,
  { split, { simp[Λ', P] },
    intros s,
    rcases (le s).is_initial_of_lt (by simp[P, P_length]) with ⟨l, ν, eqn⟩,
    have : l = [], { have := congr_arg list.length eqn, simp[P_length] at this, exact list.length_eq_zero.mp this },
    rcases this with rfl, simp at eqn, 
    refine ⟨ν, eq.symm eqn⟩ },
  exact ⟨Λ', equiv, thick⟩
end

end Path

def eventually_include {k} (μ : Tree k) (η : ℕ → Tree k) : Prop :=
∃ s₀, μ = η s₀ ∧ ∀ s ≥ s₀, μ <:+ η s

notation `lim` binders `, ` μ ` =≤ ` r:(scoped η, eventually_include μ η) := r


def eventually_include_s {k} {μ₀ : Tree k} (μ : ancestor μ₀) (η : ℕ → Tree k) : Prop :=
∃ s₀, ↑μ = η s₀ ∧ ∀ s ≥ s₀, out μ :: μ.val <:+ η (s + 1)

notation `lim` binders `, ` μ ` =< ` r:(scoped η, eventually_include_s μ η) := r


@[simp] def Tree'.is_pi : Π {k} (η : Tree' k), bool
| 0       ff       := ff
| 0       tt       := tt
| (k + 1) (η :: _) := !Tree'.is_pi η
| (k + 1) []       := ff

def Tree'.is_sigma {k} (η : Tree' k) : bool := !η.is_pi

@[simp] def Tree'.is_validated : Π {k} (η : Tree' k), bool
| 0       ff       := ff
| 0       tt       := tt
| (k + 1) (η :: _) := Tree'.is_validated η
| (k + 1) []       := ff

notation `∞` := tt

notation `𝟘` := ff

@[simp] lemma is_pi_neg {k} {η : Tree k} : !η.is_pi ↔ η.is_sigma := by simp[Tree'.is_sigma]

lemma neg_is_pi_iff {k} {η : Tree k} : ¬η.is_pi ↔ η.is_sigma :=
by { unfold Tree'.is_sigma, cases Tree'.is_pi η; simp }

@[simp] lemma is_pi_eq_ff {k} {η : Tree' k} : η.is_pi = ff ↔ η.is_sigma :=
by { unfold Tree'.is_sigma, cases Tree'.is_pi η; simp }

@[simp] lemma is_sigma_eq_ff {k} {η : Tree' k} : η.is_sigma = ff ↔ η.is_pi :=
by { unfold Tree'.is_sigma, cases Tree'.is_pi η; simp }

lemma pi_or_sigma {k} (η : Tree' k) : η.is_pi ∨ η.is_sigma :=
by { unfold Tree'.is_sigma, cases η.is_pi; simp }

lemma not_pi_sigma {k} {η : Tree' k} (pi : η.is_pi) (sigma : η.is_sigma) : false :=
by { simp only [Tree'.is_sigma] at sigma, cases η.is_pi, { exact bool.not_ff pi }, { exact bool.not_ff sigma } }

@[simp] lemma pi_cons_iff_sigma {k} {μ : Tree' k} {η : Tree k} : @Tree'.is_pi (k + 1) (μ :: η) = μ.is_sigma :=
by simp[Tree'.is_sigma]

@[simp] lemma sigma_cons_iff_pi {k} {μ : Tree' k} {η : Tree k} : @Tree'.is_sigma (k + 1) (μ :: η) = μ.is_pi :=
by simp[Tree'.is_sigma]

@[simp] lemma is_pi_iff_eq_infinity (μ : Tree' 0) : μ.is_pi ↔ μ = ∞ :=
by cases μ; simp

@[simp] lemma is_sigma_iff_eq_zero (μ : Tree' 0) : μ.is_sigma ↔ μ = 𝟘 :=
by cases μ; simp[Tree'.is_sigma]

def ancestor.pi_outcome {k} {η : Tree k} (μ : ancestor η) : bool := (out μ).is_sigma
def ancestor.sigma_outcome {k} {η : Tree k} (μ : ancestor η) : bool := (out μ).is_pi

lemma lt_or_le_of_le_of_le {k} {μ₁ μ₂ η : Tree k} (le₁ : μ₁ <:+ η) (le₂ : μ₂ <:+ η) : μ₁ ⊂ᵢ μ₂ ∨ μ₂ <:+ μ₁ :=
begin
  have lt₁ : μ₁ ⊂ᵢ (default _) :: η, from list.is_initial_cons_iff_suffix.mpr le₁,
  have lt₂ : μ₂ ⊂ᵢ (default _) :: η, from list.is_initial_cons_iff_suffix.mpr le₂,
  have : ancestor.mk' lt₁ < ancestor.mk' lt₂ ∨ ancestor.mk' lt₂ ≤ ancestor.mk' lt₁,
  from lt_or_ge (ancestor.mk' lt₁) (ancestor.mk' lt₂), simp[ancestor.lt_iff, ancestor.le_iff] at this, exact this
end

lemma trichotomous_of_le_of_le {k} {μ₁ μ₂ η : Tree k} (le₁ : μ₁ <:+ η) (le₂ : μ₂ <:+ η) : μ₁ ⊂ᵢ μ₂ ∨ μ₁ = μ₂ ∨ μ₂ ⊂ᵢ μ₁ :=
begin
  have := lt_or_le_of_le_of_le le₁ le₂, simp[list.suffix_iff_is_initial] at this,
  rcases this with (h | h | h); simp[h]
end


def Tree'.proper : ∀ {n}, Tree' n → Prop
| 0       _ := true
| 1       _ := true
| (n + 2) η := list.ordered (⊂ᵢ) η ∧
    ∀ {μ : Tree' (n + 1)}, μ ∈ η → Tree'.proper μ

namespace Tree'.proper

lemma proper_of_mem {n} {η : Tree n}
  (proper : η.proper) {μ : Tree' n} (mem : μ ∈ η) : μ.proper :=
by cases n; simp[Tree'.proper] at proper; exact proper.2 mem

lemma proper_of_cons {n} {η : Tree n} {μ : Tree' n} 
  (proper : @Tree'.proper (n + 1) (μ :: η)) : η.proper :=
by cases n; simp[Tree'.proper] at*; refine ⟨list.ordered_cons proper.1, proper.2.2⟩

@[simp] def nil (k : ℕ) : @Tree'.proper (k + 1) ([] : Tree k) := 
by cases k; simp[Tree'.proper]

def singleton {k : ℕ} (η : Tree' k) (proper : η.proper) : @Tree'.proper (k + 1) [η] :=
by cases k; simp[Tree'.proper, proper]

lemma proper_of_le {k} {η₁ η₂ : Tree k} (le : η₁ <:+ η₂) (proper : η₂.proper) : η₁.proper :=
by { cases k; simp[Tree'.proper],
     refine ⟨list.ordered_suffix le proper.1, λ μ mem, _⟩,
     have : μ ∈ η₂, { rcases le with ⟨_, rfl⟩, exact list.mem_append_right _ mem},
     exact proper.2 this }

end Tree'.proper

def Tree'.weight_aux : ∀ {k}, Tree' k → ℕ
| 0       tt := 0
| 0       ff := 1
| (k + 1) μ  := list.weight_of (@Tree'.weight_aux k) μ

variables {k : ℕ}

lemma lt_weight_aux_of_lt {μ₁ μ₂ : Tree k} (lt : μ₁ ⊂ᵢ μ₂) : μ₁.weight_aux < μ₂.weight_aux :=
list.lt_weight_of_is_initial lt

lemma lt_weight_aux_of_mem {μ : Tree' k} {η : Tree k} (lt : μ ∈ η) : μ.weight_aux < η.weight_aux :=
list.lt_weight_of_mem lt

lemma weight_aux_injective : ∀ {k}, function.injective (@Tree'.weight_aux k)
| 0       tt tt eqn := by simp[Tree'.weight_aux] at eqn
| 0       tt ff eqn := by simp[Tree'.weight_aux] at eqn; contradiction
| 0       ff tt eqn := by simp[Tree'.weight_aux] at eqn; contradiction
| 0       ff ff eqn := by simp[Tree'.weight_aux] at eqn
| (k + 1) μ₁ μ₂ eqn := list.weight_of_injective (@weight_aux_injective k) eqn

lemma ancestors_or_refl_initial_of_initial {n} {μ₁ μ₂ : Tree n} (lt : μ₁ ⊂ᵢ μ₂) :
  μ₁.ancestors_or_refl ⊂ᵢ μ₂.ancestors_or_refl :=
begin
  rcases lt with ⟨l, x, rfl⟩, induction l with a l IH,
  { simp[Tree.ancestors_or_refl] },
  { simp, refine IH.trans (by simp[Tree.ancestors_or_refl]) }
end

def Tree.weight : Π {k}, Tree k → ℕ
| 0       μ        := μ.weight_aux
| (k + 1) []       := 0
| (k + 1) (ν :: μ) := ν.weight_aux + 1

@[simp] lemma weight_nil : @Tree.weight k [] = 0 := by cases k; simp[Tree.weight, Tree'.weight_aux]

@[simp] lemma weight_cons_pos (μ : Tree' k) (η : Tree k) : 0 < Tree.weight (μ :: η) :=
by {cases k; simp[Tree.weight, Tree'.weight_aux, list.weight_of] }

lemma lt_weight_of_lt : ∀ {k} {μ₁ μ₂ : Tree k} (proper : μ₂.proper), μ₁ ⊂ᵢ μ₂ → μ₁.weight < μ₂.weight
| 0       μ₁         μ₂         _      lt := by {simp[Tree.weight], exact lt_weight_aux_of_lt lt }
| (k + 1) μ          []         _      lt := by { simp at lt, contradiction }
| (k + 1) []         (ν :: μ)   _      lt := by simp[Tree.weight]
| (k + 1) (ν₁ :: μ₁) (ν₂ :: μ₂) proper lt := by {
    simp[Tree.weight], 
    have : ν₁ ⊂ᵢ ν₂,
    { have : ν₁ ∈ μ₂, { rcases list.is_initial_cons_iff_suffix.mp lt with ⟨l, rfl⟩, simp },
      exact proper.1.2 ν₁ this },
    exact lt_weight_aux_of_lt this }

lemma lt_weight_of_mem : ∀ {k} {μ : Tree k} {η : Tree (k + 1)} (proper : η.proper), μ ∈ η → μ.weight < η.weight
| k       μ        []       _      mem := by { simp at mem, contradiction }
| k       []       (ν :: η) _      mem := by { cases k; simp[Tree.weight, Tree'.weight_aux] at mem ⊢ }
| 0       (σ :: μ) (ν :: η) proper mem := by {
    simp[Tree.weight] at mem ⊢, rcases mem with (rfl | mem),
    { simp },
    { rcases proper.1.2 (σ :: μ) mem with ⟨l, a, rfl⟩,
      refine nat.lt.step (lt_weight_aux_of_lt ⟨l, a, rfl⟩) } }
| (k + 1) (σ :: μ) (ν :: η) proper mem := by {
    simp[Tree.weight] at mem ⊢, rcases mem with (rfl | mem),
    { exact lt_weight_aux_of_mem (by simp) },
    { rcases proper.1.2 (σ :: μ) mem with ⟨_, _, rfl⟩, exact lt_weight_aux_of_mem (by simp) } }

lemma lt_weight_cons_of_lt {μ₁ μ₂ : Tree k} {η₁ η₂ : Tree (k + 1)} (lt : μ₁ ⊂ᵢ μ₂) :
  Tree.weight (μ₁ :: η₁) < Tree.weight (μ₂ :: η₂) :=
by { simp[Tree.weight], exact lt_weight_aux_of_lt lt}

