import tactic data.pfun computability.primrec data.list.basic

open encodable part

section

@[simp, reducible] def prod.unpaired {α β γ} (f : α → β → γ) : α × β → γ := λ p, f p.1 p.2

@[simp, reducible] def prod.unpaired3 {α β γ δ} (f : α → β → γ → δ) : α × β × γ → δ := λ p, f p.1 p.2.1 p.2.2

def coe_ropt {α σ} (f : α → σ) : α →. σ := λ x, part.some (f x)

prefix `↑ᵣ`:max := coe_ropt

@[simp] theorem coe_ropt_app {α σ} (f : α → σ) (a : α) : ↑ᵣf a = some (f a) := rfl

def coe_opt {α σ} (f : α → σ) : α → option σ := λ x, option.some (f x)

prefix `↑ₒ`:max := coe_opt

@[simp] theorem coe_opt_app {α σ} (f : α → σ) (a : α) : ↑ₒf a = some (f a) := rfl

def coe_opt_ropt {α σ} (f : α → option σ) : α →. σ := λ x, part.of_option (f x)

prefix `↑ʳ`:max := coe_opt_ropt

@[simp] theorem coe_opt_ropt_app {α σ} (f : α → option σ) (a : α) : ↑ʳf a = f a := rfl

def coe_ropt_opt {α σ} (f : α →. σ) [D : decidable_pred f.dom] : α → option σ := λ x, 
@part.to_option _ (f x) (D x)

prefix `↑ᵒ`:max := coe_ropt_opt

@[simp] theorem coe_ropt_opt_app {α σ} (f : α →. σ) [D : decidable_pred f.dom] (a : α) :
  ↑ᵒf a = @part.to_option _ (f a) (D a) := rfl

end

namespace list
variables {α : Type*}

def rnth (l : list α) := l.reverse.nth

def rnth_le (l : list α) (n) (h : n < l.length) : α := l.reverse.nth_le n (by simp; exact h)

def irnth [inhabited α] (l : list α) (n) : α := (l.rnth n).iget

theorem rnth_ext {l₁ l₂ : list α} (h : ∀ n, l₁.rnth n = l₂.rnth n) : l₁ = l₂ :=
list.reverse_inj.mp (list.ext h)

theorem rnth_ext' {l₁ l₂ : list α} (h : ∀ n a, l₁.rnth n = some a ↔ l₂.rnth n = some a) : l₁ = l₂ :=
rnth_ext (λ n, by
  { cases C₁ : l₁.rnth n; cases C₂ : l₂.rnth n,
    { refl },
    { exfalso, simp[(h n _).mpr C₂] at*, exact C₁ },
    { exfalso, simp[(h n _).mp C₁] at*, exact C₂ },
    { simp[(h n _).mp C₁] at*, exact C₂ } })

@[simp]
lemma rnth_nil (n) : (nil : list α).rnth n = none := rfl

@[simp]
lemma rnth_self_length (l : list α) : l.rnth l.length = none :=
by simp[rnth] 

@[simp]
lemma rnth_concat_length (n : α) (l : list α) : (n :: l).rnth l.length = some n :=
by { simp[list.rnth], 
     have : l.length = l.reverse.length, simp,
     simp only [this, list.nth_concat_length] }

lemma rnth_append {l₀ l₁ : list α} {n : ℕ} (hn : n < l₀.length) :
  (l₁ ++ l₀).rnth n = l₀.rnth n :=
by { simp[list.rnth], exact list.nth_append (by simp; exact hn) }

lemma rnth_cons {l : list α} {n : ℕ} {a} (hn : n < l.length) :
  (a :: l).rnth n = l.rnth n :=
by { simp[list.rnth], exact list.nth_append (by simp; exact hn) }

lemma rnth_le_rnth {l : list α} {n} (h : n < l.length) :
  l.rnth n = some (l.rnth_le n h) :=
by simp[list.rnth, list.rnth_le]; exact nth_le_nth _

lemma irnth_rnth [inhabited α] {l : list α} :
  ∀ {n}, n < l.length → l.rnth n = some (l.irnth n) :=
begin
  induction l with d l IH; simp,
  intros n h, have := eq_or_lt_of_le (nat.lt_succ_iff.mp h),
  cases this; simp[irnth, this],
  simp[rnth_cons this], exact IH this
end

lemma rnth_some_lt {l : list α} {n a} (h : l.rnth n = some a) : n < l.length :=
begin
  simp[list.rnth] at h, rcases list.nth_eq_some.mp h with ⟨h1, _⟩,
  simp at h1, exact h1
end

lemma rnth_none {l : list α} {n} : l.rnth n = none ↔ l.length ≤ n :=
by simp[list.rnth]

theorem rnth_map {α β} (f : α → β) : ∀ (l : list α) n, (l.map f).rnth n = (l.rnth n).map f :=
by simp [list.rnth, ←list.map_reverse]

theorem nth_find_index {α} {p : α → Prop} [decidable_pred p] {l : list α} :
  ∀ {a}, l.nth (l.find_index p) = some a → p a :=
by { induction l with b l IH; simp[list.find_index],
     by_cases C : p b; simp [C, IH], exact @IH }

theorem nth_find_index_neg {α} {p : α → Prop} [decidable_pred p] {l : list α} :
  ∀ {n} {a}, n < l.find_index p → l.nth n = some a → ¬p a :=
begin
  induction l with b l IH; simp[list.find_index],
  by_cases C : p b; simp [C], intros n a e,
  cases n; simp, { intros e, simp[←e, C] },
  have : n < list.find_index p l, from nat.succ_lt_succ_iff.mp e,
  exact IH this
end

def initial {α} (l : list α) (n : ℕ) : list α := l.drop (l.length - n)

infix `↾*`:70 := list.initial

lemma initial_elim {α} {l : list α} {n} (h : l.length ≤ n) : l↾*n = l :=
by { have : l.length - n = 0, omega, simp[list.initial, this] }

@[simp] lemma initial_0 {α} {l : list α} : l↾*0 = [] := by simp[list.initial]

lemma initial_length {α} {l : list α} {n : ℕ} (h : n < l.length) : (l↾*n).length = n :=
by simp [list.initial, h]; omega

@[simp] lemma initial_initial {α} (l : list α) (n m : ℕ) :
  (l↾*m)↾*n = l↾*(min m n) :=
begin
  simp[list.initial], congr,
  have C : n ≤ m ∨ m ≤ n, exact le_total n m, cases C; simp[C],
  { have : ∀ k, k - (k - m) - n + (k - m) = k - n,
    { intros k,
      have eqn := le_or_lt m k, cases eqn,
      { simp [nat.sub_sub_assoc (show k ≤ k, by refl) eqn,
          nat.sub_add_eq_add_sub C, nat.add_sub_cancel' eqn] },
      { have : k - m = 0, from nat.sub_eq_zero_of_le (le_of_lt eqn),
        simp[this] } },
    exact this _ },
  { have : ∀ k, k - (k - m) - n = 0,
    { intros k, 
      have eqn := le_or_lt m k, cases eqn,
      { simp [nat.sub_sub_assoc (show k ≤ k, by refl) eqn], exact nat.sub_eq_zero_of_le C },
      { have eqn1 : k - m = 0, from nat.sub_eq_zero_of_le (le_of_lt eqn),
        have eqn2 : k - n = 0, from nat.sub_eq_zero_of_le (le_of_lt $ gt_of_ge_of_gt C eqn),
        simp[eqn1, eqn2] } },
    exact this _ }
end

lemma initial_rnth_some_iff  {α} {l : list α} {n m : ℕ} {a} :
  (l↾*m).rnth n = some a ↔ l.rnth n = some a ∧ n < m :=
begin
  have eqn : l.length ≤ m ∨ m < l.length, from le_or_lt _ _,
  cases eqn,
  { simp[list.initial_elim eqn], intros h, exact gt_of_ge_of_gt eqn (rnth_some_lt h) },
  split,
  { revert eqn a m n,
    simp [list.initial],
    induction l with d l IH; simp,
    intros n m a eqn_m eqn_a,
     simp[show l.length + 1 - m = l.length - m + 1, by omega] at eqn_a,
    have C := eq_or_lt_of_le (nat.lt_succ_iff.mp eqn_m),
    cases C,
    { simp[←C] at eqn_a, simp[list.rnth_cons (list.rnth_some_lt eqn_a)],
      exact ⟨eqn_a, by simp[C]; exact rnth_some_lt eqn_a⟩ },
    { have : n < l.length, { have := list.rnth_some_lt eqn_a, simp at this, omega},
      simp[list.rnth_cons this], apply IH C eqn_a } },
  { rintros ⟨h, eq⟩,
    have :=list.reverse_take m (le_of_lt eqn),
    simp [list.initial, list.rnth, ←this] at*, simp[list.nth_take eq, h] }
end

lemma initial_rnth_some  {α} {l : list α} {n m : ℕ} {a} :
  (l↾*m).rnth n = some a → l.rnth n = some a :=
begin
  have eqn : l.length ≤ m ∨ m < l.length, from le_or_lt _ _,
  cases eqn,
  { simp[list.initial_elim eqn] },
  revert eqn a m n,
  simp [list.initial],
  induction l with d l IH; simp,
  intros n m a eqn_m eqn_a, simp[show l.length + 1 - m = l.length - m + 1, by omega] at eqn_a,
  have C := eq_or_lt_of_le (nat.lt_succ_iff.mp eqn_m),
  cases C,
  { simp[←C] at eqn_a, simp[list.rnth_cons (list.rnth_some_lt eqn_a)], exact eqn_a },
  { have : n < l.length, { have := list.rnth_some_lt eqn_a, simp at this, omega},
    simp[list.rnth_cons this], apply IH C eqn_a }
end

@[simp] lemma initial_nil {n} : (nil : list α)↾*n = nil := by simp[list.initial]

lemma initial_cons {l : list α} {d n} (h : n < l.length) : (d :: l)↾*n = l↾*n :=
by { simp[list.initial, show l.length + 1 - n = l.length - n + 1, by omega] }

@[simp] lemma initial_cons_self {l : list α} {d} : (d :: l)↾*l.length = l :=
by simp[list.initial]

def get_elem  {α} (p : α → Prop) [decidable_pred p] (l : list α) : option α :=
l.nth (l.find_index p)

@[simp] theorem get_elem_iff {α} {p : α → Prop} [decidable_pred p] {l : list α} : ∀ x,
  l.get_elem p = some x ↔
  ∃ n, l.nth n = some x ∧ p x ∧ ∀ m z, m < n → l.nth m = some z → ¬p z :=
begin
  simp [list.get_elem],
  induction l with a l IH; simp [list.find_index],
  intros x, by_cases C : p a; simp [C],
  { split, 
    { intros eqn, use 0, simp[←eqn, C] },
    { rintros ⟨n, hyp, px, hyp1⟩,
      cases n; simp at hyp, exact hyp,
      exfalso,
      have := hyp1 0 a, simp at this,
      contradiction } },
  { rw IH, split,
    { rintros ⟨n, eqn_x, px, hyp_n⟩,
      refine ⟨n+1, eqn_x, px, _⟩, 
      intros m z eqn_m eqn_z,
      cases m; simp at eqn_z, simp [←eqn_z, C],
      have : m < n, from nat.succ_lt_succ_iff.mp eqn_m,
      exact hyp_n m z this eqn_z },
    { rintros ⟨n, eqn_x, px, hyp_n⟩,
      cases n; simp at eqn_x, simp [eqn_x] at C, contradiction,
      refine ⟨n, eqn_x, px, λ m z eqn_m eqn_z, _⟩,
      have := nat.succ_lt_succ_iff.mpr eqn_m,
      exact hyp_n (m+1) z this (by simp; exact eqn_z) } }
end

@[simp] theorem get_elem_iff_none {α} {p : α → Prop} [decidable_pred p] {l : list α} :
  l.get_elem p = none ↔ ∀ n x, l.nth n = some x → ¬p x :=
begin
  simp [list.get_elem, list.find_index],
  induction l with a l IH; simp [list.find_index], by_cases C : p a;
  simp[C],
  { refine ⟨0, a, rfl, C⟩ },
  { simp [nat.succ_le_succ_iff, IH], split,
    { intros hyp n, cases n; simp[C], exact hyp n },
    { intros hyp n x eqn_x, exact hyp (n+1) x eqn_x } }
end

def fdecode {α σ} [decidable_eq α] (c : list (α × σ)) (a : α) : option σ :=
(c.get_elem (λ x : α × σ, x.fst = a)).map prod.snd
-- fdecode c a = ε b. ⟨a, b⟩ ∈ c

def sdecode {α} [decidable_eq α] (a : α) (c : list (α × bool)) : Prop := c.fdecode a = some tt
-- sdecode c a = ⟨a, tt⟩ ∈ c

@[simp] theorem fdecode_iff {α σ} [decidable_eq α] (c : list (α × σ)) {x y} :
  c.fdecode x = some y ↔
  ∃ n, c.nth n = some (x, y) ∧ ∀ m z, m < n → c.nth m ≠ some (x, z) :=
begin
  simp [list.fdecode, list.get_elem_iff], split,
  { rintros ⟨a, n, eqn_n, eqn_a, hyp⟩,
    refine ⟨n, (by simp [←eqn_a]; exact eqn_n), λ m z eqn_m eqn_m1, _⟩,
    have := hyp m (x, z) eqn_m eqn_m1, simp at this, contradiction },
  { rintros ⟨n, eqn_n, hyp⟩,
    refine ⟨x, n, eqn_n, rfl, λ m z eqn_m eqn_m1 eqn_x, _⟩,
    have := hyp m z.snd eqn_m, rw ←eqn_x at this, simp at this,
    contradiction }
end

@[simp] theorem fdecode_iff_none {α σ} [decidable_eq α] (c : list (α × σ)) {x} :
  c.fdecode x = none ↔ ∀ n y, c.nth n ≠ some (x, y) :=
begin
  simp [list.fdecode, list.get_elem_iff_none], split,
  { intros hyp n y eqn_xy, have := hyp n (x, y) eqn_xy, simp at this, contradiction },
  { intros hyp n z eqn_z eqn_z1, have := hyp n z.snd, rw ←eqn_z1 at this, simp at this,
    contradiction }
end

@[simp] theorem fdecode_cons {α σ} [decidable_eq α] (x y) (c : list (α × σ)) :
  ((x, y) :: c).fdecode x = some y :=
by simp; refine ⟨0, rfl, λ m z, by simp⟩

@[simp] def of_fn' (f : ℕ → α) : ℕ → list α
| 0     := []
| (n+1) := f n :: of_fn' n

@[simp] lemma append_cons_neq (a : α) (l₁ l₂ : list α) : l₁ ++ a :: l₂ ≠ l₂ := λ h,
begin
  have : (l₁ ++ a :: l₂).length = l₂.length, simp[h],
  simp[nat.add_left_comm l₁.length] at this, exact this
end

@[simp] lemma cons_neq (a : α) (l : list α) : a :: l ≠ l := append_cons_neq a [] l
@[simp] lemma cons_neq' (a : α) (l : list α) : l ≠ a :: l := ne.symm (cons_neq a l)

@[simp] lemma not_suffix_cons (l : list α) (a : α) : ¬ a :: l <:+ l :=
by simp[list.is_suffix, append_cons_neq]

lemma suffix_append_iff_suffix (l l₁ l₂ : list α) : l₁ ++ l <:+ l₂ ++ l ↔ l₁ <:+ l₂ :=
exists_congr $ λ r, by rw [←append_assoc, append_left_inj]

@[simp] lemma suffix_cons_iff_eq (a₁ a₂ : α) (l : list α) : a₁ :: l <:+ a₂ :: l ↔ a₁ = a₂ :=
by { have : a₁ :: l <:+ a₂ :: l ↔ [a₁] <:+ [a₂], from suffix_append_iff_suffix l [a₁] [a₂], rw this,
     split,
     { rintros ⟨⟨hd, tl⟩, h⟩, { simp* at* }, { exfalso, simp at*, exact h } },
     { rintros rfl, refine ⟨[], by simp⟩ } }

lemma suffix_antisymm {l₁ l₂ : list α} (h₁ : l₁ <:+ l₂) (h₂ : l₂ <:+ l₁) : l₁ = l₂ :=
by { rcases h₁ with ⟨l12, h₁⟩, rcases h₂ with ⟨l21, h₂⟩,
     have : (l21 ++ l12) ++ l₁ = [] ++ l₁,
     { rw [←h₁, ←append_assoc] at h₂, simp[h₂] },
     have : l21 ++ l12 = [] := list.append_right_cancel this,
     simp at this,
     simp[this] at h₁, refine h₁ }

def is_initial (l₁ l₂ : list α) : Prop := ∃ l₃ a, l₃ ++ a :: l₁ = l₂

infix ` ⊂ᵢ `:50 := is_initial

@[simp] lemma is_initial_antirefl (l : list α) : ¬ l ⊂ᵢ l := λ h,
by simp[is_initial, *] at*

@[simp] lemma not_is_initial_nil (l : list α) : ¬ l ⊂ᵢ [] := λ h,
by simp[is_initial, *] at*

lemma is_initial.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ ⊂ᵢ l₂) (h₂ : l₂ ⊂ᵢ l₃) : l₁ ⊂ᵢ l₃ :=
by { rcases h₁ with ⟨l12, a12, h₁⟩, rcases h₂ with ⟨l23, a23, h₂⟩,
     refine ⟨l23 ++ [a23] ++ l12, a12, by simp[h₁, h₂]⟩ }

lemma is_initial_of_suffix_is_initial {l₁ l₂ l₃ : list α} (h₁ : l₁ <:+ l₂) (h₂ : l₂ ⊂ᵢ l₃) : l₁ ⊂ᵢ l₃ :=
by { rcases h₁ with ⟨l12, h₁⟩,
     cases C : l12.reverse with a' l',
     { simp at C, rcases C with rfl,
       simp at h₁, rcases h₁ with rfl, exact h₂ },
     { have := congr_arg list.reverse C, simp at this, rcases this with rfl,
       rcases h₂ with ⟨l23, a23, h₂⟩, simp at h₁,
       refine ⟨l23 ++ [a23] ++ l'.reverse, a', by simp[h₁, h₂]⟩ } }

lemma suffix_of_is_initial_is_initial {l₁ l₂ l₃ : list α} (h₁ : l₁ ⊂ᵢ l₂) (h₂ : l₂ <:+ l₃) : l₁ ⊂ᵢ l₃ :=
by { rcases h₁ with ⟨l12, a12, h₁⟩, rcases h₂ with ⟨l23, h₂⟩,
     refine ⟨l23 ++ l12, a12, by simp[h₁, h₂]⟩ }


@[simp] lemma is_initial_cons (a : α) (l : list α) : l ⊂ᵢ a :: l := ⟨[], a, rfl⟩

lemma is_initial_cons_iff {x : α} {l₁ l₂ : list α} :
  l₁ ⊂ᵢ x :: l₂ ↔ l₁ = l₂ ∨ l₁ ⊂ᵢ l₂ :=
begin
  split,
  { rintro ⟨⟨hd, tl⟩, y, eqn⟩,
    { simp at eqn, refine or.inl eqn.2 },
    { simp at eqn, refine or.inr ⟨_, _, eqn.2⟩ } },
  { rintro (rfl | hl₁),
    { simp },
    { exact hl₁.trans (l₂.is_initial_cons _) } }
end

instance is_initial_decidable [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ ⊂ᵢ l₂)
| l₁ []        := is_false (not_is_initial_nil l₁)
| l₁ (a :: l₂) := 
  have IH : decidable (l₁ ⊂ᵢ l₂) := is_initial_decidable l₁ l₂,
  @dite (decidable (l₁ ⊂ᵢ (a :: l₂))) (l₁ ⊂ᵢ l₂) IH
    (λ h, is_true (h.trans (l₂.is_initial_cons _)))
    (λ h, if eqn : l₁ = l₂ then is_true (by simp[eqn])
      else is_false (by { simp[is_initial_cons_iff], exact not_or eqn h }))

lemma is_initial_of_lt_length {l : list α} {n : ℕ} (h : n < l.length) : l↾*n ⊂ᵢ l :=
begin
  simp[initial],
  cases C : (take (l.length - n) l).reverse with a l',
  { exfalso,
    have : l.length - n = 0,
    { have := congr_arg list.length C, simp at this, exact this },
    have : l.length ≤ n, exact sub_eq_zero_iff_le.mp this, 
    exact nat.lt_le_antisymm h this },
  { have : take (l.length - n) l = l'.reverse ++ [a],
    { have := congr_arg list.reverse C, simp at this, exact this },
    refine ⟨l'.reverse, a, _⟩,
    have lmm := list.take_append_drop (l.length - n) l, simp [this] at lmm,
    exact lmm }
end

lemma suffix_of_is_initial {l₁ l₂ : list α} (h : l₁ ⊂ᵢ l₂) : l₁ <:+ l₂ :=
by { rcases h with ⟨l₃, a, h⟩, refine ⟨l₃ ++ [a], by simp[h]⟩ }

lemma suffix_iff_is_initial {l₁ l₂ : list α} : l₁ <:+ l₂ ↔ l₁ ⊂ᵢ l₂ ∨ l₁ = l₂ :=
⟨begin
    revert l₁ l₂,
    suffices :
      ∀ {l l₁ l₂ : list α}, l.reverse ++ l₁ = l₂ → l₁ ⊂ᵢ l₂ ∨ l₁ = l₂,
    { intros l₁ l₂ h, rcases h with ⟨l, h⟩, exact @this l.reverse l₁ l₂ (by simp[h]) },
    intros l l₁ l₂ h, induction l with a l IH generalizing l₁ l₂,
    { right, simp* at* },
    { left, simp at h, refine ⟨l.reverse, a, h⟩ } 
  end, λ h, by { cases h, { exact suffix_of_is_initial h }, { simp[h] } } ⟩

lemma is_initial_iff_suffix {l₁ l₂ : list α} : l₁ ⊂ᵢ l₂ ↔ l₁ <:+ l₂ ∧ l₁ ≠ l₂ :=
by { simp[suffix_iff_is_initial, or_and_distrib_right], intros h₁ h₂, simp[h₂] at*, exact h₁ }

lemma rnth_eq_iff_suffix_cons_initial {l : list α} {n : ℕ} {a : α} :
  l.rnth n = a ↔ a :: l↾*n <:+ l :=
begin
  induction l with a' l IH,
  { simp, exact option.not_mem_none a },
  { have C : n < l.length ∨ n = l.length ∨ l.length < n, exact trichotomous _ _,
    cases C,
    { simp[rnth_cons C, initial_cons C, IH], split,
      { intros h, exact h.trans (list.suffix_cons a' l) },
      { intros h, have := list.suffix_cons_iff.mp h,
        cases this,
        { exfalso,
          have : l↾*n = l, { simp* at * },
          have := congr_arg list.length this, simp[initial_length C] at this,
          simp[this] at C, exact C  },
        { exact this } } },
    cases C,
    { rcases C with rfl, simp, unfold_coes, simp[option.some_inj, @eq_comm _ a a'] },
    { have : (a' :: l).length ≤ n, { simp, exact nat.succ_le_iff.mpr C },
      simp[rnth_none.mpr this, initial_elim this], exact option.not_mem_none a } }
end

lemma is_initial_length {l₁ l₂ : list α} (h : l₁ ⊂ᵢ l₂) : l₁.length < l₂.length :=
by { rcases h with ⟨l, a, h⟩, simp[←h],
     exact (length l₁).lt_add_left (length l₁ + 1) (length l) (lt_add_one (length l₁)) }

lemma eq_initial_of_is_initial {l₁ l₂ : list α} (h : l₁ ⊂ᵢ l₂) : l₂↾*l₁.length = l₁ :=
begin
  simp[initial],
  rcases h with ⟨l, a, h⟩, simp[←h, add_assoc],
  have : l.length + (l₁.length + 1) - l₁.length = l.length + 1,
  { simp[←add_assoc], omega },
  simp[this, list.drop_append]
end


end list

section rel

end rel

namespace fin

def add' {n} (i : fin n) : fin (n + 1) := ⟨i, nat.lt.step i.property⟩

lemma cases' {n} (i : fin (n + 1)) : (∃ i' : fin n, i = add' i') ∨ i = ⟨n, lt_add_one n⟩ :=
by { have : ↑i < n ∨ ↑i = n, exact nat.lt_succ_iff_lt_or_eq.mp i.property, cases this,
     { left, refine ⟨⟨i, this⟩, fin.eq_of_veq _⟩, simp[add'] },
     { right, apply fin.eq_of_veq, simp[this] } }

end fin

def finitary (α : Type*) (n : ℕ) := fin n → α

namespace finitary
variables {α : Type*}
open vector

def cons {n} (f : finitary α n) (a : α) : finitary α (n + 1) := λ i, if h : ↑i < n then f ⟨i, h⟩ else a

infixr ` ::ᶠ `:60  := finitary.cons

@[simp] lemma cons_app0 {n} (f : finitary α n) (a : α) : (f ::ᶠ a) ⟨n, lt_add_one n⟩ = a := by simp[finitary.cons]

@[simp] lemma cons_app1 {n} (f : finitary α n) (a : α) (i : fin n) : (f ::ᶠ a) i.add' = f i :=
by { simp[finitary.cons, fin.add'], intros h, exfalso, exact nat.lt_le_antisymm i.property h }

def nil : finitary α 0 := λ i, by { exfalso, exact i.val.not_lt_zero i.property }
notation `fin[` l:(foldl `, ` (h t, finitary.cons t h) nil `]`) := l

def tail {n} (f : finitary α (n + 1)) : finitary α n := λ i, f ⟨i, nat.lt.step i.property⟩
def head {n} (f : finitary α (n + 1)) : α := f ⟨n, lt_add_one n⟩

lemma tail_cons_head {n} (f : finitary α (n + 1)) : f.tail ::ᶠ f.head = f :=
funext (λ i, by { simp[cons, tail, head],
  intros h,
  congr, apply fin.eq_of_veq, simp,
  have : ↑i ≤ n, from fin.is_le i,
  exact le_antisymm h this })

@[simp] lemma zero_eq (f : finitary α 0) : f = finitary.nil :=
funext (λ i, by { have := i.property, exfalso, exact i.val.not_lt_zero this })

@[simp] lemma fin1_eq (f : finitary α 1) : fin[f 0] = f :=
funext (λ i, by { rcases i with ⟨i, i_p⟩, cases i; simp[cons], exfalso, simp[←nat.add_one] at*, exact i_p })

@[simp] lemma fin2_eq (f : finitary α 2) : fin[f 0, f 1] = f :=
funext (λ i, by { rcases i with ⟨i, i_p⟩, cases i; simp[cons], cases i, { simp },
  exfalso, simp[←nat.add_one] at i_p, exact i_p })

end finitary

def list.of_list {α : Type*} : ∀ l : list α, (fin (l.length) → α)
| []        := finitary.nil
| (a :: as) := as.of_list ::ᶠ a


section classical
local attribute [instance, priority 0] classical.prop_decidable

noncomputable def Prop_encode : Prop → ℕ := λ P, if P then 1 else 0

def Prop_decode : ℕ → option Prop
| 0       := some false
| 1       := some true
| (n + 2) := none

noncomputable instance encodable.Prop : encodable Prop :=
⟨Prop_encode, Prop_decode, λ P, by by_cases C : P; simp[C, Prop_encode, Prop_decode]⟩

theorem Prop_prim : nat.primrec (λ n, encodable.encode (encodable.decode Prop n)) :=
begin
  let f : ℕ → ℕ := (λ n, cond (n = 0) (encode $ some false)
    (cond (n = 1) (encode $ some true) (encode (none : option Prop)))),
  have : (λ n, encode (decode Prop n)) = f,
  { funext n, simp[f], cases n; simp[decode, Prop_decode],
    cases n; simp[decode, Prop_decode] },
  rw this, apply primrec.nat_iff.mp,
  refine primrec.cond
    (primrec₂.comp primrec.eq primrec.id (primrec.const _))
    (primrec.const _)
    (primrec.cond
      (primrec₂.comp primrec.eq primrec.id (primrec.const _))
      (primrec.const _)
      (primrec.const _))
end

noncomputable instance primcodable.Prop : primcodable Prop := ⟨Prop_prim⟩

end classical