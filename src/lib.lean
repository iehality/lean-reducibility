import tactic data.pfun computability.primrec data.list.basic

open encodable part

universes u v

section

@[simp, reducible] def prod.unpaired {α β γ} (f : α → β → γ) : α × β → γ := λ p, f p.1 p.2

@[simp, reducible] def prod.unpaired3 {α β γ δ} (f : α → β → γ → δ) : α × β × γ → δ := λ p, f p.1 p.2.1 p.2.2

def coe_ropt {α σ} (f : α → σ) : α →. σ := λ x, part.some (f x)

prefix `↑ᵣ`:max := coe_ropt

@[simp] theorem coe_ropt_app {α σ} (f : α → σ) (a : α) : ↑ᵣf a = some (f a) := rfl

@[simp] theorem coe_ropt_dom {α σ} (f : α → σ) : (↑ᵣf).dom = set.univ := rfl

def coe_opt {α σ} (f : α → σ) : α → option σ := λ x, option.some (f x)

prefix `↑ₒ`:max := coe_opt

@[simp] theorem coe_opt_app {α σ} (f : α → σ) (a : α) : ↑ₒf a = some (f a) := rfl

def coe_opt_ropt {α σ} (f : α → option σ) : α →. σ := λ x, part.of_option (f x)

prefix `↑ʳ`:max := coe_opt_ropt

lemma coe_opt_ropt_eq {α σ} (f : α → option σ) : ↑ʳ f = (λ x, ↑(f x)) := rfl

@[simp] theorem coe_opt_ropt_app {α σ} (f : α → option σ) (a : α) : ↑ʳf a = f a := rfl

def coe_ropt_opt {α σ} (f : α →. σ) [D : decidable_pred f.dom] : α → option σ := λ x, 
@part.to_option _ (f x) (D x)

prefix `↑ᵒ`:max := coe_ropt_opt

@[simp] theorem coe_ropt_opt_app {α σ} (f : α →. σ) [D : decidable_pred f.dom] (a : α) :
  ↑ᵒf a = @part.to_option _ (f a) (D a) := rfl

end

namespace nat

lemma least_number {p : ℕ → Prop} (ex : ∃ n, p n) : ∃ n, (∀ m, m < n → ¬ p m) ∧ p n :=
by { revert ex, contrapose, simp, intros h, exact nat.strong_rec' h }

lemma least_number' {p : ℕ → Prop} {n} (ex : p n) : ∃ n, (∀ m, m < n → ¬ p m) ∧ p n :=
nat.least_number ⟨n, ex⟩

lemma range_infinity_of_injective {f : ℕ → ℕ} (hf : function.injective f) : 
  ∀ n, ∃ m, n < f m := λ n,
begin
  have : set.inj_on f set.univ, { intros x₁ _ x₂ _ eqn, exact hf eqn },
  have : (f '' set.univ).infinite, from (set.infinite_image_iff this).mpr (set.infinite_univ),
  rcases set.infinite.exists_nat_lt this n with ⟨k, ⟨m, _, rfl⟩, lt⟩,
  exact ⟨m, lt⟩
end

end nat

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

lemma mem_iff_rnth {a : α} {l : list α} :
a ∈ l ↔ ∃ (n : ℕ), l.rnth n = some a :=
by { have := @mem_iff_nth _ a l.reverse, simp at this, exact this }

lemma rnth_none {l : list α} {n} : l.rnth n = none ↔ l.length ≤ n :=
by simp[list.rnth]

lemma rnth_cons_none {l : list α} {a} {n} : (a :: l).rnth n = none ↔ l.length < n :=
by {simp[list.rnth], exact nat.succ_le_iff }

lemma rnth_cons_some_iff {l : list α} {n : ℕ} {a a' : α} :
  (a :: l).rnth n = a' ↔ (l.rnth n = a' ∧ n < l.length) ∨ (a = a' ∧ n = l.length) :=
begin
  have C : n < l.length ∨ n = l.length ∨ l.length < n, exact trichotomous n (length l),
  cases C,
  { have : ¬n = l.length, { intros h, simp[h] at C, contradiction },
    simp[C, rnth_cons, this] },cases C,
  { rcases C with rfl, unfold_coes, simp },
  { unfold_coes, simp[C, rnth_cons_none.mpr],
    have eqn₁ : ¬ n < l.length, { intros h, exact nat.lt_asymm C h },
    have eqn₂ : ¬ n = l.length, { intros h, simp[h] at C, contradiction },
    simp[eqn₁, eqn₂] }
end

theorem rnth_map {α β} (f : α → β) : ∀ (l : list α) n, (l.map f).rnth n = (l.rnth n).map f :=
by simp [list.rnth, ←list.map_reverse]

lemma rnth_eq_nth_of_lt {l : list α} {n : ℕ} (hn : n < l.length) : l.rnth n = l.nth (l.length - 1 - n) :=
by { simp[list.rnth, rnth_le_rnth hn],
     have eqn :l.length - 1 - n < l.length, { omega },
     have : l.rnth_le n hn = l.nth_le (l.length - 1 - n) eqn,
       from list.nth_le_reverse' l n (by simp[hn]) eqn, simp[this, nth_le_nth eqn] }

lemma rnth_of_rnth_cons {l : list α} {a a' : α} {n} (h : l.rnth n = a') : (a :: l).rnth n = a' :=
by simp[rnth_cons_some_iff]; exact or.inl ⟨h, rnth_some_lt h⟩

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

@[simp] def range_r : ℕ → list ℕ
| 0       := []
| (n + 1) := n :: range_r n

lemma range_r_eq_reverse_range (n) : range_r n = (range n).reverse :=
by { induction n with n IH, { simp }, { simp[IH, list.range_succ] } }

@[simp] lemma mem_range_r_iff_mem_reverse_range (n m) : m ∈ range_r n ↔ m ∈ range n :=
by simp[range_r_eq_reverse_range]

theorem nodup_range_r (n : ℕ) : nodup (range_r n) :=
by simp[range_r_eq_reverse_range]; exact nodup_range n

@[simp] lemma length_range_r (n : ℕ) : (list.range_r n).length = n :=
by simp[range_r_eq_reverse_range]

@[simp] lemma range_r_rnth : ∀ {n i} (h : i < n), (range_r n).rnth i = some i
| (n + 1) i h := by { simp, 
    have C : i < n ∨ i = n, from lt_or_eq_of_le (nat.lt_succ_iff.mp h),
    cases C,
    { have : (n :: range_r n).rnth i = (range_r n).rnth i, from rnth_cons (by simp[C]),
      simp[this, range_r_rnth C] },
    { simp[C], have := rnth_concat_length n (range_r n), simp at this, exact this } }

def initial {α} (l : list α) (n : ℕ) : list α := l.drop (l.length - n)

infix `↾*`:70 := list.initial

lemma initial_elim {α} {l : list α} {n} (h : l.length ≤ n) : l↾*n = l :=
by { have : l.length - n = 0, omega, simp[list.initial, this] }

@[simp] lemma initial_0 {α} {l : list α} : l↾*0 = [] := by simp[list.initial]

lemma initial_length {α} {l : list α} {n : ℕ} (h : n < l.length) : (l↾*n).length = n :=
by simp [list.initial, h]; omega

@[simp] lemma le_initial_length {α} (l : list α) (n : ℕ) : (l↾*n).length ≤ n :=
by { simp[list.initial], omega }

@[simp] lemma initial_initial {α} (l : list α) (n m : ℕ) :
  (l↾*m)↾*n = l↾*(min m n) :=
begin
  simp[list.initial], congr,
  have C : n ≤ m ∨ m ≤ n, exact le_total n m, cases C; simp[C],
  { have : ∀ k, k - (k - m) - n + (k - m) = k - n,
    { intros k,
      have eqn := le_or_lt m k, cases eqn,
      { omega },
      { have : k - m = 0, from nat.sub_eq_zero_of_le (le_of_lt eqn),
        simp[this] } },
    exact this _ },
  omega
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

lemma initial_rnth_of_lt  {α} {l : list α} {n m : ℕ} (h : n < m) :
  (l↾*m).rnth n = l.rnth n :=
begin
  cases C₂ : l.rnth n,
  { have : ∀ a, ¬((l↾*m).rnth n = some a),
    { intros a, simp[initial_rnth_some_iff], simp[C₂] },
    cases (l↾*m).rnth n with x, { refl }, { exfalso, exact this x rfl } },
  { exact initial_rnth_some_iff.mpr ⟨C₂, h⟩ }
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

def get_elem {α} (p : α → Prop) [decidable_pred p] (l : list α) : option α :=
l.nth (l.find_index p)

theorem get_elem_eq_some_iff {α} {p : α → Prop} [decidable_pred p] {l : list α} {x} :
  l.get_elem p = some x ↔ ∃ n, l.nth n = some x ∧ p x ∧ ∀ m z, m < n → l.nth m = some z → ¬p z :=
begin
  simp [list.get_elem],
  induction l with a l IH generalizing x; simp [list.find_index],
  by_cases C : p a; simp [C],
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

theorem get_elem_iff_none {α} {p : α → Prop} [decidable_pred p] {l : list α} :
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

def get_elem_r {α} (p : α → Prop) [decidable_pred p] (l : list α) : option α :=
l.reverse.get_elem p

theorem get_elem_r_eq_some_iff {α} {p : α → Prop} [decidable_pred p] {l : list α} {x} :
  l.get_elem_r p = ↑x ↔ ∃ n, l.rnth n = ↑x ∧ p x ∧ ∀ m z, m < n → l.rnth m = ↑z → ¬p z :=
@get_elem_eq_some_iff _ _ _ _ x

theorem get_elem_r_eq_none_iff_rnth {α} {p : α → Prop} [decidable_pred p] {l : list α} :
  l.get_elem_r p = none ↔ ∀ n x, l.rnth n = some x → ¬p x :=
get_elem_iff_none

theorem get_elem_r_eq_none_iff_mem {α} {p : α → Prop} [decidable_pred p] {l : list α} :
  l.get_elem_r p = none ↔ ∀ x, x ∈ l → ¬p x :=
by { simp[list.mem_iff_rnth, get_elem_r_eq_none_iff_rnth], exact forall_swap }

def to_fn {α σ} [decidable_eq α] (c : list (α × σ)) (a : α) : option σ :=
(c.get_elem (λ x : α × σ, x.fst = a)).map prod.snd
-- to_fn c a = ε b. ⟨a, b⟩ ∈ c

def to_set {α} [decidable_eq α] (a : α) (c : list (α × bool)) : bool := c.to_fn a = some tt
-- to_set c a ↔ ⟨a, tt⟩ ∈ c

@[simp] theorem to_fn_iff {α σ} [decidable_eq α] (c : list (α × σ)) {x y} :
  c.to_fn x = some y ↔
  ∃ n, c.nth n = some (x, y) ∧ ∀ m z, m < n → c.nth m ≠ some (x, z) :=
begin
  simp [list.to_fn, list.get_elem_eq_some_iff], split,
  { rintros ⟨a, n, eqn_n, eqn_a, hyp⟩,
    refine ⟨n, (by simp [←eqn_a]; exact eqn_n), λ m z eqn_m eqn_m1, _⟩,
    have := hyp m (x, z) eqn_m eqn_m1, simp at this, contradiction },
  { rintros ⟨n, eqn_n, hyp⟩,
    refine ⟨x, n, eqn_n, rfl, λ m z eqn_m eqn_m1 eqn_x, _⟩,
    have := hyp m z.snd eqn_m, rw ←eqn_x at this, simp at this,
    contradiction }
end

@[simp] theorem to_fn_iff_none {α σ} [decidable_eq α] (c : list (α × σ)) {x} :
  c.to_fn x = none ↔ ∀ n y, c.nth n ≠ some (x, y) :=
begin
  simp [list.to_fn, list.get_elem_iff_none], split,
  { intros hyp n y eqn_xy, have := hyp n (x, y) eqn_xy, simp at this, contradiction },
  { intros hyp n z eqn_z eqn_z1, have := hyp n z.snd, rw ←eqn_z1 at this, simp at this,
    contradiction }
end

@[simp] theorem to_fn_cons {α σ} [decidable_eq α] (x y) (c : list (α × σ)) :
  ((x, y) :: c).to_fn x = some y :=
by simp; refine ⟨0, rfl, λ m z, by simp⟩

@[simp] def of_fn' (f : ℕ → α) : ℕ → list α
| 0     := []
| (n+1) := f n :: of_fn' n

def chr {α} [decidable_eq α] (l : list α) (a : α) : bool := a ∈ l

@[simp] lemma chr_tt_iff {α} [decidable_eq α] (l : list α) (a : α) : l.chr a = tt ↔ a ∈ l := by simp[chr]

@[simp] lemma chr_ff_iff {α} [decidable_eq α] (l : list α) (a : α) : l.chr a = ff ↔ a ∉ l := by simp[chr]

@[simp] lemma chr_app_iff {α} [decidable_eq α] (l : list α) (a : α) : l.chr a ↔ a ∈ l := by simp[chr]

lemma chr_get_elem {α} [decidable_eq α] (l : list α) : l.chr = (λ a, (l.get_elem (λ x, x = a)).is_some) :=
begin
  ext a, cases C : l.get_elem (λ x, x = a); simp,
  { simp[get_elem_iff_none, list.mem_iff_nth] at C ⊢, intros x eqn,
    have := C x a eqn, contradiction },
  { simp[get_elem_eq_some_iff] at C, rcases C with ⟨s, eqn, rfl, _⟩,
    exact nth_mem eqn }
end

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

@[simp] lemma is_initial_nil_cons (l : list α) (a : α) : [] ⊂ᵢ a :: l :=
by { cases C : l.reverse with x l',
     { have := congr_arg list.reverse C, simp at this, exact ⟨[], a, by simp[this]⟩ },
     { have := congr_arg list.reverse C, simp at this, exact ⟨[a] ++ l'.reverse, x, by simp[this]⟩ } }

lemma is_initial.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ ⊂ᵢ l₂) (h₂ : l₂ ⊂ᵢ l₃) : l₁ ⊂ᵢ l₃ :=
by { rcases h₁ with ⟨l12, a12, h₁⟩, rcases h₂ with ⟨l23, a23, h₂⟩,
     refine ⟨l23 ++ [a23] ++ l12, a12, by simp[h₁, h₂]⟩ }

lemma is_suffix.is_initial_of_is_initial {l₁ l₂ l₃ : list α} (h₁ : l₁ <:+ l₂) (h₂ : l₂ ⊂ᵢ l₃) : l₁ ⊂ᵢ l₃ :=
by { rcases h₁ with ⟨l12, h₁⟩,
     cases C : l12.reverse with a' l',
     { simp at C, rcases C with rfl,
       simp at h₁, rcases h₁ with rfl, exact h₂ },
     { have := congr_arg list.reverse C, simp at this, rcases this with rfl,
       rcases h₂ with ⟨l23, a23, h₂⟩, simp at h₁,
       refine ⟨l23 ++ [a23] ++ l'.reverse, a', by simp[h₁, h₂]⟩ } }

lemma is_initial_antisymm {l₁ l₂ : list α} (h₁ : l₁ ⊂ᵢ l₂) (h₂ : l₂ ⊂ᵢ l₁) : false :=
by { rcases h₁ with ⟨l, a, rfl⟩, rcases h₂ with ⟨l', a', eqn⟩, 
     have := congr_arg list.length eqn, simp[add_assoc] at this,
     rw (show l₁.length + (1 + 1) = (1+1) + l₁.length, from add_comm _ _) at this,
     simp[←add_assoc] at this, contradiction }

lemma is_initial.is_initial_of_suffix {l₁ l₂ l₃ : list α} (h₁ : l₁ ⊂ᵢ l₂) (h₂ : l₂ <:+ l₃) : l₁ ⊂ᵢ l₃ :=
by { rcases h₁ with ⟨l12, a12, h₁⟩, rcases h₂ with ⟨l23, h₂⟩,
     refine ⟨l23 ++ l12, a12, by simp[h₁, h₂]⟩ }

lemma is_initial.lt_length {l₁ l₂ : list α} (h : l₁ ⊂ᵢ l₂) : l₁.length < l₂.length :=
by { rcases h with ⟨l, x, rfl⟩, simp,
     exact (length l₁).lt_add_left (length l₁ + 1) (length l) (lt_add_one (length l₁))}

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
    have : l.length ≤ n,
    { have := congr_arg list.length C, simp at this, exact this },
    exact nat.lt_le_antisymm h this },
  { have : take (l.length - n) l = l'.reverse ++ [a],
    { have := congr_arg list.reverse C, simp at this, exact this },
    refine ⟨l'.reverse, a, _⟩,
    have lmm := list.take_append_drop (l.length - n) l, simp [this] at lmm,
    exact lmm }
end

lemma suffix_of_is_initial {l₁ l₂ : list α} (h : l₁ ⊂ᵢ l₂) : l₁ <:+ l₂ :=
by { rcases h with ⟨l₃, a, h⟩, refine ⟨l₃ ++ [a], by simp[h]⟩ }

lemma is_initial.suffix {l₁ l₂ : list α} (h : l₁ ⊂ᵢ l₂) : l₁ <:+ l₂ :=
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
  
lemma is_initial_suffix_antisymm {l₁ l₂ : list α} (lt : l₁ ⊂ᵢ l₂) (le : l₂ <:+ l₁) : false :=
by {cases suffix_iff_is_initial.mp le, { exact is_initial_antisymm lt h }, { simp[h] at lt, contradiction } }

lemma is_initial_cons_iff_suffix {x : α} {l₁ l₂ : list α} :
  l₁ ⊂ᵢ x :: l₂ ↔ l₁ <:+ l₂ :=
by { simp[is_initial_cons_iff, suffix_iff_is_initial], exact or.comm }

lemma suffix_cons_iff_is_initial {l₁ l₂ : list α} :
  (∃ x : α, x :: l₁ <:+ l₂) ↔ l₁ ⊂ᵢ l₂ :=
⟨λ ⟨x, l, eqn⟩, ⟨l, x, eqn⟩, λ ⟨l, a, eqn⟩, ⟨a, l, eqn⟩⟩

lemma is_initial_of_pos_suffix {l₁ l₂ l : list α}
  (h : l ++ l₁ <:+ l₂) (pos : 0 < l.length) : l₁ ⊂ᵢ l₂ :=
begin
    cases C : l.reverse with a l IH,
    { exfalso, simp at C, rcases C with rfl, simp at pos, contradiction },
    { have := congr_arg list.reverse C, simp at this, rcases this with rfl,
      rcases h with ⟨l', rfl⟩,
      exact ⟨l' ++ l.reverse, a, by simp⟩ }
end

lemma is_suffix.is_initial_of_lt {l₁ l₂ : list α}
  (h : l₁ <:+ l₂) (lt : l₁.length < l₂.length) : l₁ ⊂ᵢ l₂ :=
begin
  rcases h with ⟨l, rfl⟩,
  induction l with a l IH, { exfalso, simp at lt, contradiction },
  { simp[is_initial_cons_iff_suffix] }
end

lemma is_suffix.eq_of_eq {l₁ l₂ : list α}
  (h : l₁ <:+ l₂) (lt : l₁.length = l₂.length) : l₁ = l₂ :=
begin
  exact eq_of_suffix_of_length_eq h lt
end

lemma is_suffix.le_length {l₁ l₂ : list α} (h : l₁ <:+ l₂) : l₁.length ≤ l₂.length :=
by { rcases h with ⟨l, rfl⟩, simp }

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

lemma suffix_initial (l : list α) (n : ℕ) : l↾*n <:+ l :=
by { simp[initial], exact drop_suffix (length l - n) l }

lemma map_suffix {α β} {l l' : list α} (f : α → β) (h : l <:+ l') :
  l.map f <:+ l'.map f :=
begin
  rcases h with ⟨l'', h⟩,
  refine ⟨map f l'', _⟩, simp[←h]
end

lemma mem_of_suffix {l₁ l₂ : list α} (h : l₁ <:+ l₂) {a : α} (mem : a ∈ l₁) : a ∈ l₂ :=
by { rcases h with ⟨l, rfl⟩, simp[mem] }

def incomparable (l₁ l₂ : list α) : Prop := ¬l₁ <:+ l₂ ∧ ¬l₂ <:+ l₁

infix ` ∥ ` :50 := incomparable

lemma incomparable_iff_suffix_is_initial {l₁ l₂ : list α} :
  l₁ ∥ l₂ ↔ ¬l₁ ⊂ᵢ l₂ ∧ ¬l₂ <:+ l₁ :=
⟨λ ⟨h₁, h₂⟩, ⟨λ A, h₁ (suffix_of_is_initial A), h₂⟩,
  λ ⟨h₁, h₂⟩, ⟨λ A, by { simp[is_initial_iff_suffix] at h₁, simp[h₁ A, suffix_refl] at h₂, contradiction }, h₂⟩⟩

@[simp] lemma incomparable.antirefl {l : list α} : ¬ l ∥ l :=
by simp[incomparable]

lemma incomparable.symm {l₁ l₂ : list α} :
  l₁ ∥ l₂ → l₂ ∥ l₁ := λ ⟨h₁, h₂⟩, ⟨h₂, h₁⟩

lemma incomparable.symm_iff {l₁ l₂ : list α} :
  l₁ ∥ l₂ ↔ l₂ ∥ l₁ := ⟨incomparable.symm, incomparable.symm⟩

lemma incomparable_iff_is_initial_suffix {l₁ l₂ : list α} :
  l₁ ∥ l₂ ↔ ¬l₁ <:+ l₂ ∧ ¬l₂ ⊂ᵢ l₁ :=
⟨λ h, by simp[incomparable_iff_suffix_is_initial.mp h.symm], λ h,
  incomparable.symm (incomparable_iff_suffix_is_initial.mpr (by simp[h]))⟩

lemma incomparable_trichotomy (l₁ l₂ : list α) : l₁ <:+ l₂ ∨ l₂ ⊂ᵢ l₁ ∨ l₁ ∥ l₂ :=
by { simp[incomparable_iff_is_initial_suffix], by_cases C₁ : l₁ <:+ l₂; simp[C₁], by_cases C₂ : l₂ ⊂ᵢ l₁; simp[C₂] }

lemma incomparable_of_le_of_le {l₁ l₂ k₁ k₂ : list α} (h : l₁ ∥ l₂) (le₁ : l₁ <:+ k₁) (le₂ : l₂ <:+ k₂) :
  k₁ ∥ k₂ :=
begin
  simp[incomparable], rcases h with ⟨i₁, i₂⟩,
  rcases le₁ with ⟨m₁, rfl⟩, rcases le₂ with ⟨m₂, rfl⟩,
  by_contradiction, 
  have C : m₁ ++ l₁ <:+ m₂ ++ l₂ ∨ m₂ ++ l₂ <:+ m₁ ++ l₁, from or_iff_not_and_not.mpr h,
  cases C,
  { have : l₁ <:+ l₂ ∨ l₂ <:+ l₁,
      from list.suffix_or_suffix_of_suffix ((list.suffix_append m₁ l₁).trans C) (list.suffix_append m₂ l₂),
    cases this; contradiction },
  { have : l₂ <:+ l₁ ∨ l₁ <:+ l₂,
      from list.suffix_or_suffix_of_suffix ((list.suffix_append m₂ l₂).trans C) (list.suffix_append m₁ l₁),
    cases this; contradiction }
end

lemma incomparable_of_lt {l₁ l₂ : list α} (lt : l₁ ⊂ᵢ l₂) {a : α} (h : a ∉ l₂)  : a :: l₁ ∥ l₂ :=
begin
  simp[incomparable], by_contradiction A,
  have : a :: l₁ <:+ l₂ ∨ l₂ <:+ a :: l₁, from or_iff_not_and_not.mpr A,
  cases this,
  { rcases this with ⟨l, rfl⟩, simp at h, contradiction },
  { rcases list.suffix_cons_iff.mp this with (rfl | hh), {simp at h, contradiction },
    { exact is_initial_suffix_antisymm lt hh } }
end

def ordered (r : α → α → Prop) : list α → Prop
| []       := true
| (a :: l) := ordered l ∧ (∀ a', a' ∈ l → r a' a)

@[simp] lemma ordered_nil {r : α → α → Prop} : [].ordered r :=
by simp[ordered]

@[simp] lemma ordered_singleton {r : α → α → Prop} (a : α) : [a].ordered r :=
by simp[ordered]

lemma ordered_cons {r : α → α → Prop} {l : list α} {a : α} (o : (a :: l).ordered r) : l.ordered r :=
by simp[ordered] at o; exact o.1

lemma ordered_suffix {r : α → α → Prop} {l₁ l₂ : list α} (le : l₁ <:+ l₂) (o : l₂.ordered r) : l₁.ordered r :=
begin
  rcases le with ⟨l, rfl⟩,
  induction l with a l IH,
  { exact o },
  { simp[ordered] at o, exact IH o.1 }
end

lemma ordered_mono {r : α → α → Prop} {l : list α} (o : l.ordered r) :
  ∀ {n m : ℕ} (lt : n < m) {a₁ a₂ : α} (h₁ : l.rnth n = a₁) (h₂ : l.rnth m = a₂), r a₁ a₂ :=
begin
  suffices :
    ∀ n m {a₁ a₂ : α} (h₁ : l.rnth n = a₁) (h₂ : l.rnth (n + 1 + m) = a₂), r a₁ a₂,
    { intros n m lt, have := @this n (m - (n + 1)),
      have le : n + 1 ≤ m, from nat.succ_le_iff.mpr lt,
      simp[nat.add_sub_of_le le] at this, exact @this },
  intros n m a₁ a₂ eqn₁ eqn₂, induction l with a l IH generalizing n m a₁ a₂,
  { simp at eqn₂, exfalso, exact option.not_mem_none a₂ eqn₂ },
  { simp[ordered] at o,
    have lt : n < l.length, { have := rnth_some_lt eqn₂, simp at this,
      simp[nat.succ_add n m, ←nat.add_one] at this, exact buffer.lt_aux_1 this },
    have eqn₁ : l.rnth n = ↑a₁, { simp[lt, rnth_cons] at eqn₁, exact eqn₁ },
    simp[rnth_cons, lt, rnth_cons_some_iff] at eqn₂, cases eqn₂,
    { exact IH o.1 _ _ eqn₁ eqn₂.1 },
    { rcases eqn₂ with ⟨rfl, eqn₂⟩, refine o.2 _ (mem_iff_rnth.mpr ⟨n, eqn₁⟩) } }
end

lemma ordered_isomorphism {r : α → α → Prop} [is_irrefl α r] [is_asymm α r] {l : list α} (o : l.ordered r)
  {n m : ℕ} {a₁ a₂ : α} (h₁ : l.rnth n = a₁) (h₂ : l.rnth m = a₂) : n < m ↔ r a₁ a₂ :=
begin
  have C : n < m ∨ n = m ∨ m < n, from trichotomous n m,
  cases C,
  { simp[C], exact ordered_mono o C h₁ h₂ }, cases C,
  { rcases C with rfl, 
    have : a₁ = a₂, { simp[h₁] at h₂, exact option.some_inj.mp h₂ },
    simp[this], exact irrefl a₂ },
  { have : ¬n < m, { intros h, exact nat.lt_asymm C h },
    simp[this],
    intros A,
    have : r a₂ a₁, from ordered_mono o C h₂ h₁, exact asymm A this }
end

lemma ordered_filter {r : α → α → Prop} (p : α → Prop) [decidable_pred p] : ∀ {l : list α}
  (h : l.ordered r), (l.filter p).ordered r 
| []       h := by simp
| (a :: l) h := by { simp[filter] at h ⊢,
    by_cases C : p a; simp[C, ordered],
    { exact ⟨ordered_filter h.1, λ a' mem pa', h.2 _ mem⟩ },
    { exact ordered_filter h.1 } }

lemma ordered_map {α β} {r : α → α → Prop} {r' : β → β → Prop} (f : α → β)
  (isom : ∀ x y, r x y → r' (f x) (f y)) : ∀ {l : list α} (o : l.ordered r), (l.map f).ordered r'
| []       o := by simp
| (a :: l) o := by { simp[ordered] at o ⊢, refine ⟨ordered_map o.1, λ a' mem, isom _ _ (o.2 _ mem)⟩ }

def weight_of (wt : α → ℕ) : list α → ℕ
| []       := 0
| (a :: l) := nat.mkpair (wt a) l.weight_of + 1

@[simp] lemma weight_of_nil (wt : α → ℕ) : ([] : list α).weight_of wt = 0 := rfl

lemma lt_weight_of_is_initial {wt : α → ℕ} {l₁ l₂ : list α} (lt : l₁ ⊂ᵢ l₂) : l₁.weight_of wt < l₂.weight_of wt :=
begin
  rcases lt with ⟨l, x, rfl⟩, induction l with y l IH; simp[weight_of],
  { exact nat.lt_succ_iff.mpr (nat.right_le_mkpair (wt x) (weight_of wt l₁)) },
  { exact nat.lt_succ_iff.mpr (le_of_lt (gt_of_ge_of_gt (nat.right_le_mkpair (wt y) (weight_of wt (l ++ x :: l₁))) IH)) }
end

lemma lt_weight_of_mem {wt : α → ℕ} {a : α} {l : list α} (lt : a ∈ l) : wt a < l.weight_of wt :=
begin
  induction l with x l IH,
  { simp at lt, contradiction },
  { simp at lt, rcases lt with (rfl | mem); simp[weight_of],
    exact nat.lt_succ_iff.mpr (nat.left_le_mkpair (wt a) (weight_of wt l)),
    refine nat.lt_succ_iff.mpr (le_of_lt (gt_of_ge_of_gt (nat.right_le_mkpair (wt x) (l.weight_of wt)) (IH mem))) }
end

lemma weight_of_injective {wt : α → ℕ} (inj : function.injective wt) : function.injective (list.weight_of wt)
| []         []         eqn := rfl
| []         (a :: l)   eqn := by { exfalso, simp[weight_of] at eqn, exact ne.symm (nat.succ_ne_zero _) eqn }
| (a :: l)   []         eqn := by { exfalso, simp[weight_of] at eqn, exact eqn }
| (a₁ :: l₁) (a₂ :: l₂) eqn := by { simp[weight_of] at eqn,
    have eqn := congr_arg nat.unpair eqn, simp at eqn,
    have eqn₁ : a₁ = a₂, from inj eqn.1,
    have eqn₂ : l₁ = l₂, from weight_of_injective eqn.2,
    simp[eqn₁, eqn₂] }

end list

namespace option
variables {α : Type u}

@[simp] lemma some_ne_none' (x : α) : ¬ (↑x : option α) = none := option.some_ne_none x
@[simp] lemma some_ne_none'' (x : α) : ¬ none = (↑x : option α) := ne.symm (option.some_ne_none x)

@[simp] theorem some_inj' {a b : α} : (↑a : option α) = ↑b ↔ a = b := by unfold_coes; simp
@[simp] theorem some_inj'' {a b : α} : ↑a = some b ↔ a = b := by unfold_coes; simp
@[simp] theorem some_inj''' {a b : α} : some a = ↑b ↔ a = b := by unfold_coes; simp

end option

class omega_ordering (α : Type u) :=
(ordering : α → ℕ)
(inj : function.injective ordering)
#check omega_ordering.ordering

namespace omega_ordering

def default (α : Type*) [encodable α] : omega_ordering α := ⟨encodable.encode, encode_injective⟩

instance {α : Type u} [omega_ordering α] : linear_order α :=
{ le := λ x y, (omega_ordering.ordering x) ≤ (omega_ordering.ordering y),
  lt := λ x y, (omega_ordering.ordering x) < (omega_ordering.ordering y),
  le_refl := λ x, le_refl (omega_ordering.ordering x),
  le_trans := λ x y z, by { simp, exact le_trans },
  lt_iff_le_not_le := λ x y, by { simp, exact le_of_lt },
  le_antisymm := λ x y h₁ h₂,
    by { have := @le_antisymm ℕ _ _ _ h₁ h₂, exact omega_ordering.inj this },
  le_total := λ x y, @le_total ℕ _ _ _,
  decidable_le := λ x y,
    @has_le.le.decidable ℕ _ (omega_ordering.ordering x) (omega_ordering.ordering y) }

lemma le_iff {α} [omega_ordering α] {a b : α} :
  a ≤ b ↔ (omega_ordering.ordering a) ≤ (omega_ordering.ordering b) := by refl

lemma lt_iff {α} [omega_ordering α] {a b : α} :
  a < b ↔ (omega_ordering.ordering a) < (omega_ordering.ordering b) := by refl

def Min {α : Type u} (o : omega_ordering α) : list α → option α
| []       := none
| (a :: l) := if h : (Min l).is_some then some (min a (option.get h)) else a

lemma min_some_of_pos {α : Type u} (o : omega_ordering α) : ∀ (l : list α) (h : 0 < l.length), (o.Min l).is_some
| []       h := by exfalso; simp at h; contradiction
| (a :: l) h := by { simp[Min],  cases C : o.Min l; simp[C], unfold_coes, simp }

def Min_le {α : Type u} (o : omega_ordering α) (l : list α) (h : 0 < l.length) : α :=
option.get (min_some_of_pos o l h)

variables {α : Type u} {o : omega_ordering α}

@[simp] lemma min_none_iff : ∀ l : list α, o.Min l = none ↔ l = []
| []       := by simp[Min]
| (x :: l) := by { simp[Min], cases C : o.Min l; simp[C], }

@[simp] lemma mem_of_Min_iff_le : ∀ {l : list α} {m : α}, o.Min l = some m ↔ m ∈ l ∧ ∀ a ∈ l, m ≤ a
| []       _ := by simp[Min]
| (x :: l) m := by { simp[Min], cases C : o.Min l with m'; simp[C],
    { simp at C, simp[C], refine ⟨λ eqn, by simp[eqn], λ eqn, by simp[eqn]⟩ },
    { have : m' ∈ l ∧ ∀ (a : α), a ∈ l → m' ≤ a, from mem_of_Min_iff_le.mp C, rcases this with ⟨IH₁, IH₂⟩,
      by_cases C₁ : x ≤ m'; simp[min, C₁, min_default],
      { split,
        { rintros rfl, simp, intros a mem, exact le_trans C₁ (IH₂ a mem) },
        { rintros ⟨(h₁ | h₁), h₂, h₃⟩, { simp[h₁] },
          { have : m = m', { exact le_antisymm (h₃ m' IH₁) (IH₂ m h₁) }, rcases this with rfl,
            exact le_antisymm C₁ h₂ } } },
      { split,
        { rintros rfl, exact ⟨or.inr IH₁, le_of_not_ge C₁, IH₂⟩ },
        { rintros ⟨(h₁ | h₁), h₂, h₃⟩, {exfalso, rcases h₁ with rfl, exact C₁ (h₃ m' IH₁) },
          { exact le_antisymm (IH₂ m h₁) (h₃ m' IH₁) } } } } }

lemma Min_le_mem (o : omega_ordering α) (l : list α) {h} : o.Min_le l h ∈ l :=
(mem_of_Min_iff_le.mp (option.mem_def.mp (option.get_mem (min_some_of_pos o l h)))).1

lemma Min_le_minimum (o : omega_ordering α) {l : list α} {h} : ∀ a ∈ l, o.Min_le l h ≤ a :=
(mem_of_Min_iff_le.mp (option.mem_def.mp (option.get_mem (min_some_of_pos o l h)))).2
 
lemma eq_Min_sequence (o : omega_ordering α) (A : ℕ → list α) (pos : ∀ s, 0 < (A s).length)
  (hA₁ : ∀ s t, s < t → ¬o.Min_le (A s) (pos s) ∈ A t)
  {a : α} (mem : a ∈ A 0) (hA₂ : ∀ s, a ≠ o.Min_le (A s) (pos s) → a ∈ A s → a ∈ A (s + 1)) :
  ∃ s, a = o.Min_le (A s) (pos s) :=
begin
  suffices : ¬∀ s, a ∈ A s,
  { revert this, contrapose, simp, intros h s,
    induction s with s IH, { exact mem },
    { exact hA₂ s (h s) IH } },
  intros mem,
  have lt : ∀ s, o.Min_le (A s) (pos s) < a,
  { intros s, have : o.Min_le (A s) (pos s) ≤ a, from o.Min_le_minimum a (mem s),
    have C : o.Min_le (A s) (pos s) < a ∨ o.Min_le (A s) (pos s) = a, from lt_or_eq_of_le this,
    rcases C with (C | rfl),
    { exact C }, { exfalso, exact (hA₁ s (s + 1) (lt_add_one s)) (mem (s + 1)) } },
  have : function.injective (λ s, ordering (o.Min_le (A s) (pos s))),
  { intros s₁ s₂ eqn, simp at eqn,
    have C : s₁ < s₂ ∨ s₁ = s₂ ∨ s₂ < s₁, exact trichotomous s₁ s₂, cases C,
    { exfalso,
      have : o.Min_le (A s₁) (pos s₁) ∉ A s₂, from hA₁ s₁ s₂ C,
      have : o.Min_le (A s₁) (pos s₁) ∈ A s₂, rw inj eqn, from o.Min_le_mem _,
      contradiction }, cases C,
    { exact C },
    { exfalso,
      have : o.Min_le (A s₂) (pos s₂) ∉ A s₁, from hA₁ s₂ s₁ C,
      have : o.Min_le (A s₂) (pos s₂) ∈ A s₁, rw ← inj eqn, from o.Min_le_mem _,
      contradiction } },
  have : ∃ s, a < o.Min_le (A s) (pos s), from nat.range_infinity_of_injective this (ordering a),
  rcases this with ⟨s, eqn⟩,
  exact nat.lt_asymm (lt s) eqn
end

end omega_ordering
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

def eq_under {α : Sort*} (n : ℕ) (f g : ℕ → α) : Prop := ∀ x < n, f x = g x

notation f ` =[<` n `]` g := eq_under n f g

lemma part.opt_exists {α} (p : part α) : ∃ o : option α, (o : part α) = p :=
by { by_cases p.dom, refine ⟨p.get h, by { unfold_coes, simp [part.of_option]}⟩,
     exact ⟨none, by { unfold_coes, simp [part.of_option, part.eq_none_iff'.mpr h] }⟩ }

noncomputable def part.to_opt {α} (p : part α) : option α := classical.some (part.opt_exists p)

@[simp] lemma part.to_opt_eq {α} (p : part α) : (p.to_opt : part α) = p := classical.some_spec p.opt_exists

def list.of_list {α : Type*} : ∀ l : list α, (fin (l.length) → α)
| []        := finitary.nil
| (a :: as) := as.of_list ::ᶠ a



namespace function

#check set.infinite_image_iff

end function