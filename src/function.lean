import rpartrec coding

open encodable denumerable part

def encode2 {α σ} [encodable α] [inhabited α] [encodable σ] (f : α →. σ) :=
(λ n, (f $ (decode α n).get_or_else (default α)).map encode)

def encode2_total {α σ}  [encodable α] [inhabited α] [encodable σ] (f : α → σ) :=
(λ n, encode (f $ (decode α n).get_or_else (default α)))

@[simp] lemma encode2_total_eq {α σ} [encodable α] [inhabited α] [encodable σ] (f : α → σ) : 
  encode2 (f : α →. σ) = pfun.lift (encode2_total f) := funext (λ x, by simp[encode2, encode2_total])

theorem rpartrec.encode2_rpartrec_in {α σ} [primcodable α] [primcodable σ] [inhabited α] (f : α →. σ) :
  encode2 f partrec_in f :=
begin
  simp only [encode2],
  have c₀ : (λ n, f ((decode α n).get_or_else (default α))) partrec_in f :=
  rpartrec.refl.comp ((computable.decode.option_get_or_else $ computable.const $ default α).to_rpart),
  have c₁ : computable (λ x, encode x.2 : ℕ × σ → ℕ) := computable.encode.comp computable.snd,
  exact c₀.map c₁.to_rpart
end

theorem rpartrec.rpartrec_in_encode2 {α σ} [primcodable α] [primcodable σ]  [inhabited α] (f : α →. σ) :
  f partrec_in encode2 f :=
begin
  let f' : α →. σ := (λ a, (encode2 f (encode a)).bind (λ x, decode σ x)),
  have c₀ : (λ a, encode2 f (encode a) : α →. ℕ) partrec_in encode2 f :=
  rpartrec.refl.comp (partrec.to_rpart computable.encode),
  have c₁ : partrec₂ (λ x y, ↑(decode σ y) : α → ℕ →. σ) := computable.decode.of_option.comp computable.snd,
  exact ((c₀.bind c₁.to_rpart).of_eq $ λ a, by simp[encode2])
end

def graph {α β} [decidable_eq β] (f : α → β) : α × β → bool :=
λ x, to_bool (f x.1 = x.2)

def epsilon_r {β} [primcodable β] [inhabited β] (p : β →. bool) : part β := 
  ((nat.rfind $ λ x, p ((decode β x).get_or_else (default β))).map 
    (λ x, (decode β x).get_or_else (default β)))

def epsilon {β} [primcodable β] [inhabited β] (p : β → bool) : part β :=
epsilon_r (p : β →. bool)

theorem epsilon_witness {β} [primcodable β] [inhabited β] {p : β → bool} {b : β} :
  b ∈ epsilon p → p b = tt :=
by { simp[epsilon,epsilon_r], intros x h hl he, rw he at h, simp[←h] }

@[simp] theorem exists_epsilon_iff {β} [primcodable β] [inhabited β] {p : β → bool} :
  (epsilon p).dom ↔ (∃ b, p b = tt) := by { split,
{ intros w, use (epsilon p).get w, exact epsilon_witness ⟨w, rfl⟩ },
{ rintros ⟨b, hb⟩, simp[epsilon,epsilon_r, part.map, part.some],
  use (encode b), simp[hb], use trivial} }

@[simp] def initialpart {α σ} [denumerable α] (f : α → option σ) : ℕ → list (α × σ)
| 0       := []
| (n + 1) := option.cases_on (f (of_nat α n)) (initialpart n) (λ a, (of_nat α n, a) :: initialpart n)

infix `↾`:70 := initialpart

@[simp] theorem nat.initialpart_length {α σ} [denumerable α] (f : α → option σ) (s) : (f↾s).length ≤ s :=
by { induction s with m ih; simp,
     cases C : f (of_nat _ m); simp, { exact nat.le_succ_of_le ih},
     { exact nat.succ_le_succ ih } }

lemma nat.initialpart_nth {α σ} [denumerable α] {f : α → option σ} {s n : ℕ} {a}
  (h : n < s) (hn : f (of_nat α n) = some a) :
  ∃ i, (f↾s).nth i = some (of_nat α n, a) ∧ ∀ j b, j < i → (f↾s).nth j ≠ some (of_nat α n, b) :=
begin
  induction s with s IH,
  { simp at h, contradiction },
  { simp[initialpart], cases C : f (of_nat α s) with v; simp,
    { have : n < s ∨ n = s, from nat.lt_succ_iff_lt_or_eq.mp h,
      cases this,
      { exact IH this },
      { exfalso, simp[this, C] at hn, exact hn } },
    { have eqn_n : n < s ∨ n = s, from nat.lt_succ_iff_lt_or_eq.mp h,
      cases eqn_n,
      { rcases IH eqn_n with ⟨i, eqn_na, hi⟩, use i + 1, simp, refine ⟨eqn_na, λ j b eqn_j, _⟩,
        cases j; simp, 
        { intros e, exfalso, 
          have : n = s, rw ←@denumerable.encode_of_nat α _ s,
            rw ←@denumerable.encode_of_nat α _ n, simp [e],
          simp[this] at eqn_n, exact eqn_n },
        { have : j < i, from nat.succ_lt_succ_iff.mp eqn_j,
          exact hi _ _ this } },
      { use 0, simp[eqn_n], rw eqn_n at hn, simp[C] at hn, exact hn } } }
end

lemma nat.initialpart_nth_none {α σ} [denumerable α] {f : α → option σ} (s) {n}
  (hn : f (of_nat α n) = none) : ∀ i a, (f↾s).nth i ≠ some (of_nat α n, a) :=
begin
  induction s with s IH generalizing n; simp[initialpart],
  { cases C : f (of_nat α s) with v; simp, exact IH hn,
    intros i, cases i; simp,
    { intros a e, exfalso, simp [e, hn] at C, exact C },
    { exact IH hn i } }
end

lemma nat.initialpart_to_fn {α σ} [decidable_eq α] [denumerable α] {f : α → option σ} {s a b}
  (h : encode a < s) (hn : f a = some b) : (f↾s).to_fn a = some b :=
by simp; rw (show a = of_nat α (encode a), by simp) at hn ⊢; exact nat.initialpart_nth h hn

lemma nat.initialpart_to_fn_none {α σ} [decidable_eq α] [denumerable α] {f : α → option σ} {a}
  (ha : f a = none) (s) : (f↾s).to_fn a = none :=
by simp; rw (show a = of_nat α (encode a), by simp) at ha ⊢;
   intros m y; exact nat.initialpart_nth_none s ha m y

def list.subseq {α} [decidable_eq α] (f : ℕ → α) : list α → bool
| []      := tt
| (x::xs) := to_bool (x = f xs.length) && list.subseq xs

notation l` ⊂ₘ `f:80 := list.subseq f l

def list.subseq_t {σ} [primcodable σ] (f : ℕ → σ) :=
list.subseq (λ x, encode $ f x)

notation l` ⊂ₘ* `f:80 := list.subseq_t f l

theorem subseq_iff (l : list ℕ) (f : ℕ → ℕ) :
  l ⊂ₘ f ↔ (∀ n, n < l.length → l.rnth n = some (f n)) :=
begin
  induction l with n0 l0 ih; simp[list.subseq], split; assume h,
  { intros n h0,
    have ih0 : ∀ {n}, n < l0.length → l0.rnth n = option.some (f n), from ih.mp h.2,
    have e : n < l0.length ∨ n = l0.length, omega,
    cases e,
    simp[list.rnth, list.nth_append (show n < l0.reverse.length, by simp[list.length_reverse, e])],
    exact ih0 e,
    simp[e, list.rnth_concat_length, h.1] },
  have lm0 : n0 = f l0.length,
  { have h' := h l0.length (lt_add_one (list.length l0)),
    simp [list.rnth_concat_length] at h',
    exact option.some_inj.mp (by simp; exact h') },
  have lm1 : (l0 ⊂ₘ f) = tt,
  { apply ih.mpr, intros n ne,
    have h' := h n (nat.lt.step ne), rw ← h',
    simp[list.rnth], symmetry, exact list.nth_append (by simp[ne]) },
  exact ⟨lm0, lm1⟩
end

def nat.rfind_fin0 (p : ℕ → bool) (m : ℕ) : ℕ → option ℕ
| 0     := none
| (n+1) := cond (p (m - n.succ)) (some (m - n.succ)) (nat.rfind_fin0 n)

def nat.rfind_fin (p : ℕ → bool) (m : ℕ) := nat.rfind_fin0 p m m

theorem rfind_fin0_iff (p : ℕ → bool) : ∀ (i m n : ℕ), i ≤ m → 
  (nat.rfind_fin0 p m i = some n ↔ (m - i ≤ n ∧ n < m ∧ p n = tt ∧ ∀ l, m - i ≤ l → l < n → p l = ff)) :=
begin
  intros i, 
  induction i with i0 ih,
  { intros m n, simp [nat.rfind_fin0], intros c c0, exfalso, exact nat.lt_le_antisymm c0 c },
  { intros m n i0e, simp[nat.rfind_fin0],
    cases ep : p (m - i0.succ), simp,
    { rw ih m n (show i0 ≤ m, by omega), split, 
      { rintros ⟨e0, e1, e2, h0⟩,
        have l0 : ∀ (l : ℕ), m ≤ l + i0.succ → l < n → p l = ff,
        { intros l el0 el1,
          have le : m - i0.succ = l ∨ m - i0 ≤ l, omega,
          cases le, simp[←ep, le], simp at*,  exact h0 _ le el1 },
        exact ⟨show m ≤ n + i0.succ, by omega, e1, e2, l0⟩ },
      { rintros ⟨e0, e1, e2, h0⟩, split,
        { have l0 : m - i0.succ = n ∨ m - i0 ≤ n, omega, cases l0,
          { exfalso, simp[l0, e2] at ep, exact ep },
          { exact l0 } },
        { have l0 : ∀ (l : ℕ), m - i0 ≤ l → l < n → p l = ff := λ _ _ el1, h0 _ (by omega) el1,
          exact ⟨e1, e2, l0⟩ } } },
    { simp, split,
      { assume e, rcases e with rfl,
        exact ⟨by omega, by omega, ep,
        by { intros k l0 l1, exfalso, 
             have : m < m, from lt_of_le_of_lt l0 (lt_tsub_iff_right.mp l1), exact nat.lt_asymm this this }⟩ },
      { rintros ⟨e0, e1, e2, h0⟩,
        have l0 : m - i0.succ < n ∨ m - i0.succ = n, omega,
        cases l0,
        { exfalso, have c : p (m - i0.succ) = ff , exact h0 _ (by simp[nat.sub_add_cancel i0e]) l0,
          exact bool_iff_false.mpr c ep },
        { exact l0 } } } }
end

@[simp] theorem rfind_fin_iff {p : ℕ → bool} {m n : ℕ} :
  nat.rfind_fin p m = some n ↔ n < m ∧ p n = tt ∧ ∀ {l : ℕ}, l < n → p l = ff :=
by { have h := rfind_fin0_iff p m m n (by refl), simp at h, exact h }

@[simp] theorem rfind_fin_none  {p : ℕ → bool} {m : ℕ} :
  nat.rfind_fin p m = none ↔ ∀ {l : ℕ}, l < m → p l = ff :=
begin
  rcases e : nat.rfind_fin p m,
  { simp, assume l el, cases epl : p l, refl,
    exfalso, rcases nat_bool_minimum' epl with ⟨m0, en, em0, hm0⟩,
    have l0 : ¬nat.rfind_fin p m = some m0, { rw e, intros c, exact option.not_mem_none _ c },
    have nc := λ n, not_congr (@rfind_fin_iff p m n), simp[-rfind_fin_iff] at nc, 
    have l1 : ∃ (x : ℕ), x < m0 ∧ p x = tt := (nc _).mp l0 (by omega) em0,
    rcases l1 with ⟨n, hn, en⟩,
    have c : p n = ff := hm0 _ hn,
    exact bool_iff_false.mpr c en },
  { simp, use this,
    rw rfind_fin_iff at e, exact ⟨e.1, e.2.1⟩ }
end

namespace primrec

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem list_get_elem {f : α → list β} {p : α → β → Prop}
  [∀ a b, decidable (p a b)]
  (hf : primrec f) (hp : primrec_rel p) :
  primrec (λ a, (f a).get_elem (p a)) :=
list_nth.comp hf (list_find_index hf hp)

theorem list_rnth : primrec₂ (@list.rnth α) := 
primrec.list_nth.comp (primrec.list_reverse.comp primrec.fst) primrec.snd

def subseq {α} (A B : ℕ → option α) := ∀ n b, A n = some b → B n = some b

infix ` ⊆* `:50 := subseq

end primrec

namespace rpartrec

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem epsilon_r_rpartrec [inhabited β] (p : α × β →. bool) :
  (λ a, epsilon_r (λ x, p (a, x))) partrec_in p :=
begin
  have c₀ : (λ x, p (x.1, (decode β x.2).get_or_else (default β)) : α × ℕ →. bool) partrec_in p :=
  (rpartrec.refl.comp $ (computable.pair computable.fst 
    ((computable.decode.comp computable.snd).option_get_or_else (computable.const (default β))))
    .to_rpart),
  have c₁ : computable (λ x, (decode β x.2).get_or_else (default β) : α × ℕ → β) :=
  (computable.decode.comp computable.snd).option_get_or_else (computable.const (default β)),
  have c₂ : (λ a, nat.rfind $ λ x, p (a, (decode β x).get_or_else (default β))) partrec_in p, from rfind c₀,
  exact c₂.map c₁.to_rpart
end

theorem epsilon_r_rpartrec_refl [inhabited β] {p : α → β →. bool} :
  (λ a, epsilon_r (p a)) partrec_in prod.unpaired p :=
begin
  have c₀ : (λ x, p x.1 ((decode β x.2).get_or_else (default β)) : α × ℕ →. bool) partrec_in prod.unpaired p :=
  (rpartrec.refl.comp $ (computable.pair computable.fst 
    ((computable.decode.comp computable.snd).option_get_or_else (computable.const (default β))))
    .to_rpart),
  have c₁ : computable (λ x, (decode β x.2).get_or_else (default β) : α × ℕ → β) :=
  (computable.decode.comp computable.snd).option_get_or_else (computable.const (default β)),
  have c₂ : (λ a, nat.rfind $ λ x, p a ((decode β x).get_or_else (default β))) partrec_in prod.unpaired p, from rfind c₀,
  exact c₂.map c₁.to_rpart
end

@[rcomputability]
protected theorem epsilon_r [inhabited β] {p : α → β →. bool} {g : γ →. σ}
  (hp : p partrec₂_in g) : (λ a, epsilon_r (p a)) partrec_in g :=
epsilon_r_rpartrec_refl.trans hp

@[rcomputability]
protected theorem epsilon [inhabited β] {p : α → β → bool} {g : γ →. σ}
  (hp : p computable₂_in g) :
  (λ a, epsilon (p a)) partrec_in g :=
epsilon_r_rpartrec_refl.trans hp

theorem epsilon_rpartrec [inhabited β] (p : α × β → bool) :
  (λ a, epsilon (λ x, p (a, x))) partrec_in (λ x, some $ p x) :=
epsilon_r_rpartrec _  

end rpartrec

namespace rcomputable

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ] [primcodable τ] [primcodable μ]

@[rcomputability]
protected theorem epsilon [inhabited β] {p : α → β → bool} {g : γ →. σ} (hp : p computable₂_in g) :
  (λ a, epsilon (p a)) partrec_in g :=
rpartrec.epsilon_r hp

@[rcomputability]
theorem initialpart {α} [denumerable α] {f : α → option σ} {g : β →. τ}
  (hf : f computable_in g) : (↾) f computable_in g :=
begin
  let I : ℕ → list (α × σ) := (λ n : ℕ, n.elim []
    (λ m IH, option.cases_on (f (of_nat α m)) IH (λ a, (of_nat α m, a) :: IH))),
  have : I computable_in g,
  { refine rcomputable.nat_elim'
      rcomputable.id
      (rcomputable.const _) _, simp,
    refine rcomputable.option_cases
      (hf.comp ((primrec.of_nat _).to_rcomp.comp $ fst.comp snd))
      (snd.comp snd) _,
    refine (primrec.list_cons.comp (((primrec.of_nat _).comp $ primrec.fst.comp $
      primrec.snd.comp primrec.fst).pair primrec.snd) $ primrec.snd.comp $
      primrec.snd.comp primrec.fst).to_rcomp },
  exact (this.of_eq $ λ n, by induction n with n IH; simp[I]; simp[←IH])
end

theorem initialpart_s {α β} [primcodable α] [denumerable β] {f : α → β → option γ} {g : α → ℕ} {o : σ →. τ}
  (hf : f computable₂_in o) (hg : g computable_in o) : (λ x, (f x)↾(g x)) computable_in o :=
begin
  let I : α → list (β × γ) := (λ a : α, (g a).elim []
    (λ m IH, option.cases_on (f a (of_nat β m)) IH (λ a, (of_nat β m, a) :: IH))),
  have : I computable_in o,
  { refine rcomputable.nat_elim' hg (const []) (by { 
    simp,
    refine rcomputable.option_cases (hf.comp fst ((rcomputable.of_nat β).comp fst.to_unary₂)) snd.to_unary₂
    (rcomputable₂.list_cons.comp₂ (((rcomputable.of_nat β).comp fst.to_unary₂).to_unary₁.pair id'.to_unary₂)
    (to_unary₁ snd.to_unary₂)) }) },
  exact (this.of_eq $ λ n, by { simp[I], induction (g n) with n IH; simp[I]; simp[←IH]})
end

private lemma list.concat_induction {α} {C : list α → Sort*} :
  C [] → (Π l t, C l → C (l.concat t)) → Π l, C l :=
begin
  assume h0 ih,
  have l0 : Π l, C (list.reverse l),
  { intros l, induction l with hd tl tlih,
    simp, exact h0, 
    rw (show (hd :: tl).reverse = tl.reverse.concat hd, by simp), exact ih _ _ tlih },
  intros l, rw (show l = l.reverse.reverse, by simp), exact l0 _
end

theorem foldr' [inhabited α] (f : α × β → β) :
  (λ x, list.foldr (λ y z, f (y, z)) x.1 x.2 : β × list α → β) computable_in (f : α × β →. β) :=
  let foldr' := (λ x, nat.elim x.1 
    (λ y IH, f ((x.2.reverse.nth y).get_or_else (default α), IH))
    x.2.length : β × list α → β) in
  have c₀ : computable (λ x, x.2.length : β × list α → ℕ) :=
  computable.list_length.comp computable.snd,
  have c₁ : computable (λ x, x.1 : β × list α → β) := computable.fst,
  have c₂ : computable (λ x, (x.1.2.reverse.nth x.2.1).get_or_else (default α) :
    (β × list α) × ℕ × β → α) :=
  primrec.option_get_or_else.to_comp.comp
    (computable.list_nth.comp 
      (computable.list_reverse.comp $ computable.snd.comp computable.fst)
      (computable.fst.comp computable.snd)) (computable.const $ default α),
  have c₃ : (λ x, f (((x.1.2.reverse.nth x.2.1).get_or_else (default α)), x.2.2) :
    (β × list α) × ℕ × β → β) computable_in (f : α × β →. β) :=
  refl.comp (pair c₂.to_rcomp (snd.comp snd)),
  have c₄ : foldr' computable_in (f : α × β →. β) := nat_elim c₀.to_rcomp c₁.to_rcomp c₃,
  have e : ∀ a (l m : list α), nat.elim a
    (λ y IH, f (((l ++ m).nth y).get_or_else (default α), IH)) l.length =
    nat.elim a (λ y IH, f ((l.nth y).get_or_else (default α), IH)) l.length,
  { intros a,
    apply @list.concat_induction _ (λ l, ∀ m, nat.elim a 
      (λ y IH, f (((l ++ m).nth y).get_or_else (default α), IH)) l.length = 
      nat.elim a (λ y IH, f ((l.nth y).get_or_else (default α), IH)) l.length); simp,
    intros ll ld lih m, apply congr, refl, apply congr,
    { rw (show ll ++ ld :: m = ll ++ [ld] ++ m, by simp),
      rw (list.nth_append (show ll.length < (ll ++ [ld]).length, by simp)),
      rw list.nth_concat_length, refl },
    { simp [lih] } },
(c₄.of_eq $ by 
{ simp[foldr'], intros a l, induction l with ld ll lih; simp,
  rw (show ll.length = ll.reverse.length, by simp), congr,
  { rw list.nth_concat_length, refl },
  { rw e, simp[lih] } })

theorem foldr0 [inhabited α] (f : α × β → β) (b : β) :
  (λ x, list.foldr (λ y z, f (y, z)) b x : list α → β) computable_in (f : α × β →. β) := 
(foldr' f).comp (pair (const b) id)

@[rcomputability]
theorem list_foldr' [inhabited α] {f : α → β → β} {o : σ →. τ} (hf : f computable₂_in o) :
  list.foldr f computable₂_in o :=
rcomputable₂.trans₂ (foldr' (prod.unpaired f)).to₂ hf

@[rcomputability]
theorem list_foldr [inhabited β] {f : α → β → γ → γ} {g : α → γ} {h : α → list β} {o : σ →. τ}
  (hf : (prod.unpaired3 f) computable_in o) (hg : g computable_in o) (hh : h computable_in o) :
  (λ x : α, list.foldr (f x) (g x) (h x)) computable_in o :=
begin
  have eqn: ∀ (a : α) (H₁ H₂ : list β),
    nat.elim (g a) (λ y IH, f a ((H₁.reverse ++ H₂).nth y).iget IH) H₁.length = 
    nat.elim (g a) (λ y IH, f a (H₁.reverse.nth y).iget IH) H₁.length,
  { intros a H₁ H₂,
    induction H₁ with hd H₁ IH generalizing a H₂; simp,
    { have eq_hd : (H₁.reverse ++ [hd]).nth H₁.length = hd,
      { rw [show H₁.length = H₁.reverse.length, by simp, list.nth_concat_length H₁.reverse hd], refl },
      have eq_hd' : (H₁.reverse ++ hd :: H₂).nth H₁.length = hd,
      { rw [show H₁.reverse ++ hd :: H₂ = H₁.reverse ++ [hd] ++ H₂,by simp,
            list.nth_append (show H₁.length < (H₁.reverse ++ [hd]).length, by simp)], simp[eq_hd] },
      simp[eq_hd, eq_hd', IH] } },
  have : (λ a, nat.elim (g a) (λ y IH, f a ((h a).rnth y).iget IH) (h a).length) computable_in o,
  { refine rcomputable.nat_elim' (list_length.comp hh) hg
    (unpaired3 hf fst (option_iget.comp (rcomputable₂.list_rnth.comp (to_unary₁ hh) fst.to_unary₂)) snd.to_unary₂) },
  exact this.of_eq (by { 
    intros a, induction (h a) with h H IH,
    { simp }, simp[←IH, list.rnth, eqn], congr,
    { rw [show H.length = H.reverse.length, by simp, list.nth_concat_length] } })
end

@[rcomputability]
lemma list_map [inhabited β] {g : α → β → γ} {f : α → list β} {o : σ →. τ}
  (hg : g computable₂_in o) (hf : f computable_in o) :
(λ a : α, list.map (g a) (f a)) computable_in o :=
have (λ a, list.foldr (λ b s, g a b :: s) [] (f a)) computable_in o,
{ refine list_foldr
  (rcomputable₂.list_cons.comp (rcomputable₂.comp hg fst fst.to_unary₂) snd.to_unary₂) (const list.nil) hf },
this.of_eq (λ a, by simp[list.map_eq_foldr])  

@[rcomputability]
lemma list_filter [inhabited β] {p : α → β → Prop} [∀ x y, decidable (p x y)] {f : α → list β} {o : σ →. τ}
  (hp : (λ a b, to_bool (p a b)) computable₂_in o) (hf : f computable_in o) :
(λ a : α, list.filter (p a) (f a)) computable_in o :=
have (λ a, list.foldr (λ b s, if (p a b) then (b :: s) else s) [] (f a)) computable_in o,
{ refine list_foldr _ (by rcomputability) hf,
  { refine rcomputable.ite (hp.comp fst (fst.to_unary₂))
    (rcomputable₂.list_cons.comp fst.to_unary₂ snd.to_unary₂) snd.to_unary₂ } },
this.of_eq (λ a, by simp[list.filter_eq_foldr])  

@[rcomputability]
lemma list_rec [inhabited β] {f : α → list β} {g : α → γ} {h : α → β → list β → γ → γ} {o : σ →. τ}
  (hf : f computable_in o) (hg : g computable_in o) (hh : prod.unpaired4 h computable_in o) :
  @rcomputable _ _ γ _ _ _ _ _ (λ a : α, list.rec_on (f a) (g a) (h a)) o :=
let F (a : α) := (f a).foldr
  (λ (b : β) (s : list β × γ), (b :: s.1, h a b s.1 s.2)) ([], g a) in
have F computable_in o,
  from list_foldr ((rcomputable₂.list_cons.comp fst.to_unary₂ (fst.comp snd.to_unary₂)).pair hh)
    ((const list.nil).pair hg) hf,
(snd.comp this).of_eq (λ a, by { 
  suffices : F a = (f a, list.rec_on (f a) (g a) (λ b l IH, h a b l IH)), { rw this },
  simp[F], induction (f a); simp* })

@[rcomputability]
lemma omega_ordering_Min [inhabited α] (r : omega_ordering α) {o : σ →. τ}
  (hr : r.ordering computable_in o) :
  r.Min computable_in o :=
begin
  let F : list α → option α := list.foldr
    (λ (a : α) (IH : option α), option.cases_on IH a
    (λ ih, if omega_ordering.ordering a ≤ omega_ordering.ordering ih then a else ih)) none,
  have : F computable_in o,
  { simp[F],
    refine list_foldr (option_cases snd.to_unary₂ ((option_some.comp rpartrec.some).comp fst.to_unary₂) _) (const none) id',
    { refine rcomputable.ite _ _ _,
      { refine rcomputable₂.to_bool_nat_le.comp (comp hr (fst.comp snd.to_unary₁)) (to_unary₂ hr) },
      { exact option_some.comp (fst.comp snd.to_unary₁) },
      exact (option_some.comp rpartrec.some).to_unary₂ } },
  exact this.of_eq (λ l, by { induction l with x l IH, { simp[F, omega_ordering.Min] },
    { simp[F, omega_ordering.Min] at IH ⊢, rw[IH], cases C : r.Min l; simp,
      { simp[omega_ordering.min_iff],
        by_cases C : omega_ordering.ordering x ≤ omega_ordering.ordering val; simp[C] } } })
end

@[rcomputability]
lemma omega_ordering_Min_le [inhabited α] (r : omega_ordering α) (f : β → list α) (h : ∀ x, (f x).length > 0) {o : σ →. τ}
  (hr : r.ordering computable_in o) (hf : f computable_in o) :
  (λ x, r.Min_le (f x) (h x)) computable_in o :=
rcomputable.option_get ((omega_ordering_Min r hr).comp hf)

@[rcomputability]
lemma rcomputable.list_initial [inhabited α] {o : σ →. τ} : ((↾*) : list α → ℕ → list α) computable₂_in o :=
begin
  let lindex : list α → list (α × ℕ) := λ l, list.rec_on l [] (λ a l IH, (a, l.length) :: IH),
  let F : list α → ℕ → list α := λ l n, ((lindex l).filter (λ p : α × ℕ, p.2 < n)).map prod.fst,
  have : F computable₂_in o,
  { refine list_map (fst.to_unary₂)
      (list_filter (rcomputable₂.to_bool_nat_lt.comp (snd.to_unary₂) (snd.to_unary₁))
      (list_rec fst (const [])
      (rcomputable₂.list_cons.comp (pair fst.to_unary₂ (list_length.comp (fst.comp snd.to_unary₂)))
        (snd.comp snd.to_unary₂)))) },
  exact this.of_eq (λ l n, by { 
    induction l with x l IH; simp[F, lindex, list.filter],
    { have : @list.rec α (λ _, list (α × ℕ)) [] (λ (a : α) (l : list α), list.cons (a, l.length)) (x :: l) = 
        (x, l.length) :: lindex l, from rfl,
      simp[show @list.rec α (λ _, list (α × ℕ)) [] (λ (a : α) (l : list α), list.cons (a, l.length)) (x :: l) = 
        (x, l.length) :: lindex l, from rfl, list.filter],
      by_cases C : l.length < n; simp[C],
      { simp[show (x :: l)↾*n = x :: l, from list.initial_elim (nat.succ_le_iff.mpr C),
             show l↾*n = l, from list.initial_elim (le_of_lt C),
             F, lindex] at IH ⊢, exact IH },
      { have : (x :: l)↾*n = l↾*n, from list.initial_cons (not_lt.mp C),
        rw this, exact IH } } })
end

@[rcomputability]
lemma list_weight_of [inhabited α] {wt : α → ℕ} {o : σ →. τ}
  (h : wt computable_in o) : list.weight_of wt computable_in o :=
begin
  let F : list α → ℕ := λ l, list.rec_on l 0 (λ a l IH, nat.mkpair (wt a) IH + 1),
  have : F computable_in o,
  { refine rcomputable.list_rec id (const 0) _,
    exact rcomputable₂.nat_add.comp
      (rcomputable₂.comp rpartrec.some (comp h fst.to_unary₂) (snd.comp snd.to_unary₂))
      (const 1) },
  exact this.of_eq (λ l, by { induction l with x l IH; simp[F, list.weight_of], { simp[F] at IH, simp[IH] } })
end

@[rcomputability]
theorem list_chr [decidable_eq α] [inhabited α] {o : σ →. τ} :
  (list.chr : list α → α → bool) computable₂_in o :=
begin
  let F : list α → α → bool := λ l a, l.filter (λ x, x = a) ≠ [],
  have : F computable₂_in o,
  { simp[F],
    refine (dom_fintype bnot).comp₂
      ((rcomputable₂.to_bool_eq _).comp
        (rcomputable.list_filter ((rcomputable₂.to_bool_eq _).comp snd snd.to_unary₁) fst) (const [])) },
  exact this.of_eq (λ l a, by simp[F, list.filter_eq_nil, list.chr])
end

@[rcomputability]
theorem graph_rcomp [decidable_eq β] (f : α → β) : graph f computable_in (f : α →. β) :=
  have c₀ : (λ x, to_bool (x.1 = x.2) : β × β → bool) computable_in (f : α →. β) := primrec.eq.to_rcomp,
  have c₂ : (λ x, (f x.1, x.2) : α × β → β × β) computable_in (f : α →. β) := rcomputable.pair 
  (rcomputable.refl.comp rcomputable.fst) rcomputable.snd,
c₀.comp c₂

@[rcomputability]
theorem subseq_rcomputable [decidable_eq α] [inhabited α] (f : ℕ → α) :
  list.subseq f computable_in! f :=
begin
  let g := (λ x, (x.2.1 + 1, x.2.2 && graph f (x.2.1, x.1)) : α × ℕ × bool → ℕ × bool),
  let subseq0 := (λ x, (list.foldr (λ y z, g (y, z)) (0, tt) x) : list α → ℕ × bool),
  let subseq1 := (λ x, (subseq0 x).2),
  have cg : g computable_in (f : ℕ →. α) := ((computable.succ.to_rcomp).comp (fst.comp snd)).pair 
  ((primrec.to_rcomp (primrec.dom_bool₂ band)).comp $
    (snd.comp snd).pair $
      (rcomputable.graph_rcomp f).comp ((fst.comp snd).pair fst)),
  have cic : subseq1 computable_in (f : ℕ →. α) := rcomputable.snd.comp (
    list_foldr (cg.comp (pair fst.to_unary₂ snd.to_unary₂)) ((const 0).pair (const tt)) id),
  have e : ∀ l, subseq0 l = (l.length, list.subseq f l),
  { intros l, simp[subseq0], induction l with ld ll ihl; simp[list.subseq,graph],
    rw ihl, simp, rw bool.band_comm, simp [eq_comm], congr },
  exact (cic.of_eq $ λ l, by simp[subseq1,e])
end

private lemma rfind_fin0 {p : α → ℕ → bool} {f : α → ℕ} {g : α → ℕ} {h : β →. τ}
  (hp : prod.unpaired p computable_in h) (hf : f computable_in h) (hg : g computable_in h) :
  (λ a, nat.rfind_fin0 (p a) (f a) (g a) : α → option ℕ) computable_in h :=
begin
  let f₁ : α × ℕ × option ℕ → option ℕ :=
    (λ x, cond (p x.1 (f x.1 - x.2.1.succ)) (some $ f x.1 - x.2.1.succ) x.2.2),
  have c₁ : f₁ computable_in h,
  { refine rcomputable.cond
      (hp.comp (fst.pair ((primrec.to_rcomp primrec.nat_sub).comp $
        (hf.comp fst).pair (computable.succ.to_rcomp.comp $ fst.comp snd))))
        (primrec.option_some.to_rcomp.comp ((primrec.to_rcomp primrec.nat_sub).comp $
        (hf.comp fst).pair (computable.succ.to_rcomp.comp $ fst.comp snd))) (snd.comp snd) },
  have e : ∀ a b n, nat.elim option.none (λ y IH, cond (p a (b - y.succ)) (some $ b - y.succ) IH) n = 
    nat.rfind_fin0 (p a) b n,
  { intros a b n, simp, induction n with n0 ih; simp[nat.rfind_fin0], rw ih },
  have c₂ := nat_elim hg (const option.none) c₁,
  exact (c₂.of_eq $ λ n, by simp[f₁]; simp; rw e)
end

@[rcomputability]
theorem rfind_fin {p : α → ℕ → bool} {f : α → ℕ} {g : β →. τ}
  (hp : p computable₂_in g) (hf : f computable_in g) :
  (λ a, nat.rfind_fin (p a) (f a)) computable_in g := 
rfind_fin0 hp hf hf

end rcomputable

open nat.rpartrec primrec
variables {α : Type*} {σ : Type*} {β : Type*} {τ : Type*} {γ : Type*} {μ : Type*} {ν : Type*} {o_dom : Type*} {o_cod : Type*}
  [primcodable α] [primcodable σ] [primcodable β] [primcodable τ] [primcodable γ] [primcodable μ] [primcodable ν] [primcodable o_dom] [primcodable o_cod]
  {o : o_dom →. o_cod}

axiom rcomputable.code_rec {f : α → code} {fo : α → σ} {fz : α → σ} {fs : α → σ} {fl : α → σ} {fr : α → σ}
  {fp : α → code → code → σ → σ → σ} {fc : α → code → code → σ → σ → σ} {fpr : α → code → code → σ → σ → σ} {frf : α → code → σ → σ}
  (hfo : fo computable_in o) (hfz : fz computable_in o) (hfs : fs computable_in o) (hfl : fl computable_in o) (hfr : fr computable_in o)
  (hfp : prod.unpaired5 fp computable_in o) (hfc : prod.unpaired5 fc computable_in o) (hfpr : prod.unpaired5 fpr computable_in o)
  (hfrf : prod.unpaired3 frf computable_in o) :
  @rcomputable α _ σ _ _ _ _ _ (λ a, code.rec_on (f a) (fo a) (fz a) (fs a) (fl a) (fr a) (fp a) (fc a) (fpr a) (frf a)) o

-- !!!! AXIOM !!!!
axiom primrec.evaln_to_fn :
  primrec (λ x : ℕ × list (ℕ × ℕ) × code × ℕ, code.evaln x.1 x.2.1.to_fn x.2.2.1 x.2.2.2)

theorem computable.evaln_to_fn
  {s : α → ℕ} {l : α → list (ℕ × ℕ)} {c : α → code} {n : α → ℕ}
  (hs : computable s) (hl : computable l) (hc : computable c) (hn : computable n) :
  computable (λ x, code.evaln (s x) (l x).to_fn (c x) (n x)) :=
primrec.evaln_to_fn.to_comp.comp (hs.pair $ hl.pair $ hc.pair hn)

theorem eval_eq_rfind (f : ℕ → option ℕ) (c n) :
  code.eval f c n = nat.rfind_opt (λ s, code.evaln s f c n) :=
part.ext $ λ x, begin
  refine code.evaln_complete.trans (nat.rfind_opt_mono _).symm,
  intros a m n hl, apply code.evaln_mono hl,
end

theorem partrec.eval_to_fn {α} [primcodable α]
  {l : α → list (ℕ × ℕ)} {c : α → code} {n : α → ℕ}
  (hl : computable l) (hc : computable c) (hn : computable n) :
  partrec (λ x, code.eval (l x).to_fn (c x) (n x)) :=
begin
  let f := (λ x, nat.rfind_opt (λ s, code.evaln s (l x).to_fn (c x) (n x))),
  have : partrec f := (partrec.rfind_opt $
    computable.evaln_to_fn computable.snd
    (hl.comp computable.fst) (hc.comp computable.fst) (hn.comp computable.fst)),
  exact (this.of_eq $ by simp[f, eval_eq_rfind])
end

theorem list.to_fn_map [decidable_eq σ] [denumerable σ]
  (f : τ → option μ) (c : list (σ × τ)) (n) :
  (c.to_fn n).map f = (c.map (λ x : σ × τ, (x.1, f x.2))).to_fn n :=
begin
  cases C : c.to_fn n with v; simp; symmetry,
  { simp [list.to_fn_iff_none] at C ⊢, intros m o x y eqn_xy eqn_n,
    have := C m y, simp [eqn_n] at eqn_xy, contradiction },
  { simp [list.to_fn_iff] at C ⊢, rcases C with ⟨m, eqn_nv, hyp⟩,
    refine ⟨m, ⟨n, v, eqn_nv, rfl, rfl⟩, λ k p eqn_k x y eqn_xy eqn_n eqn_p, _⟩,
    have := hyp _ y eqn_k, rw [eqn_n] at eqn_xy, contradiction }
end

theorem list.to_fn_encode_of_nat {σ} [decidable_eq σ] [denumerable σ]
  (c : list (σ × τ)) :
  (λ n, option.map encode (c.to_fn (of_nat σ n))) = 
  (c.map (λ x : σ × τ, (encode x.1, encode x.2))).to_fn :=
begin
  funext n,
  cases C : c.to_fn (of_nat σ n) with v; simp; symmetry,
  { simp [list.to_fn_iff_none] at C ⊢, intros m k x y eqn_xy eqn_n eqn_k,
    have := C m y, rw ←eqn_n at this, simp at this, contradiction },
  { simp [list.to_fn_iff] at C ⊢, rcases C with ⟨m, eqn_nv, hyp⟩,
    refine ⟨m, ⟨_, _, eqn_nv, (by simp), rfl⟩, λ k z eqn_k x y eqn_xy eqn_n eqn_z, _⟩,
    have := hyp _ y eqn_k, rw ←eqn_n at this, simp at this, contradiction }
end

theorem computable.univn_to_fn (α σ) [primcodable α] [primcodable σ] {β} [decidable_eq β] [denumerable β]
  {i : γ → ℕ} {l : γ → list (β × τ)} {s : γ → ℕ} {n : γ → α}
  (hi : computable i) (hl : computable l) (hs : computable s) (hn : computable n) :
  computable (λ x : γ, (⟦i x⟧*(l x).to_fn [s x] (n x) : option σ)) :=
begin
  simp [univn, list.to_fn_encode_of_nat],
  refine computable.option_bind (computable.evaln_to_fn hs
    ((list_map primrec.id ((primrec.encode.comp $ fst.comp snd).pair
      (primrec.encode.comp $ snd.comp snd)).to₂).to_comp.comp hl)
    ((primrec.of_nat _).to_comp.comp hi)
    (primrec.encode.to_comp.comp hn))
    (primrec.decode.comp snd).to_comp
end

theorem partrec.univ_to_fn (α σ) [primcodable α] [decidable_eq σ] [denumerable σ]
  {i : γ → ℕ} {l : γ → list (σ × τ)} {n : γ → α}
  (hi : computable i) (hl : computable l) (hn : computable n) :
  partrec (λ x : γ, (⟦i x⟧*(l x).to_fn (n x) : part σ)) :=
begin
  simp [univ, list.to_fn_encode_of_nat],
  refine partrec.bind (partrec.eval_to_fn
  ((list_map primrec.id ((primrec.encode.comp $ fst.comp snd).pair
    (primrec.encode.comp $ snd.comp snd)).to₂).to_comp.comp hl)
  ((primrec.of_nat _).to_comp.comp hi)
  (primrec.encode.to_comp.comp hn))
  ((primrec.of_nat _).comp snd).to_comp
end

theorem rcomputable.evaln_w {s : α → ℕ} {f : ℕ → option ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hs : s computable_in o) (hf : f computable_in o) (hc : c computable_in o) (hn : n computable_in o) : 
  (λ x, code.evaln (s x) f (c x) (n x)) computable_in o :=
begin
  let u := (λ x, code.evaln (s x) (f↾(s x)).to_fn (c x) (n x)),
  have eqn_u : (λ x, code.evaln (s x) f (c x) (n x)) = u,
  { suffices :
      ∀ t d, code.evaln t (f↾t).to_fn d = code.evaln t f d,
    { funext, simp[u] at this ⊢, rw this },
    intros t d,
    apply code.evaln_use,
    intros u eqn_u,
    { cases C : f u,
      { exact nat.initialpart_to_fn_none C t },
      { exact nat.initialpart_to_fn (show encode u < t, from eqn_u) C } } },
  rw eqn_u,
  simp only [u],
  let m := (λ x, (s x, f↾s x, c x, n x)),
  have lmm_m : m computable_in o := (rcomputable.pair hs 
    (((rcomputable.initialpart hf).comp hs).pair (rcomputable.pair hc hn))),
  have := computable.evaln_to_fn fst.to_comp (fst.comp snd).to_comp
    (fst.comp $ snd.comp snd).to_comp (snd.comp $ snd.comp snd).to_comp,
  have := this.to_rcomp.comp lmm_m,
  exact this
end

theorem rcomputable.evaln_s {s : α → ℕ} {f : α → ℕ → option ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hs : s computable_in o) (hf : f computable₂_in o) (hc : c computable_in o) (hn : n computable_in o) : 
  (λ x, code.evaln (s x) (f x) (c x) (n x)) computable_in o :=
begin
  let u := (λ x, code.evaln (s x) ((f x)↾(s x)).to_fn (c x) (n x)),
  have eqn_u : (λ x, code.evaln (s x) (f x) (c x) (n x)) = u,
  { suffices :
      ∀ x t d, code.evaln t ((f x)↾t).to_fn d = code.evaln t (f x) d,
    { funext, simp[u] at this ⊢, rw this }, 
    intros x t d,
    apply code.evaln_use,
    intros u eqn_u,
    { cases C : f x u,
      { exact nat.initialpart_to_fn_none C t },
      { exact nat.initialpart_to_fn (show encode u < t, from eqn_u) C } } },
  rw eqn_u,
  simp only [u],
  let m := (λ x, (s x, (f x)↾s x, c x, n x)),
  have lmm_m : m computable_in o := (rcomputable.pair hs 
    (rcomputable.pair (rcomputable.initialpart_s hf hs) (hc.pair hn))),
  have := computable.evaln_to_fn fst.to_comp (fst.comp snd).to_comp
    (fst.comp $ snd.comp snd).to_comp (snd.comp $ snd.comp snd).to_comp,
  have := this.to_rcomp.comp lmm_m,
  exact this
end

theorem rcomputable.evaln_tot {s : α → ℕ} {f : ℕ → ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hs : s computable_in o) (hf : f computable_in o) (hc : c computable_in o) (hn : n computable_in o) : 
  (λ x, code.evaln (s x) ↑ₒf (c x) (n x)) computable_in o := 
rcomputable.evaln_w hs (rcomputable.option_some_iff.mpr hf) hc hn

theorem rcomputable.evaln_tot_s {s : α → ℕ} {f : α → ℕ → ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hs : s computable_in o) (hf : f computable₂_in o) (hc : c computable_in o) (hn : n computable_in o) : 
  (λ x, code.evaln (s x) ↑ₒ(f x) (c x) (n x)) computable_in o := 
rcomputable.evaln_s hs (rcomputable.option_some_iff.mpr hf) hc hn

theorem rpartrec.eval_w {f : ℕ → option ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hf : f computable_in o) (hc : c computable_in o) (hn : n computable_in o) :
  (λ x, code.eval f (c x) (n x)) partrec_in o :=
begin
  let p := (λ x, nat.rfind_opt (λ s, code.evaln s f (c x) (n x))),
  have : p partrec_in o,
  { apply rpartrec.rfind_opt, 
    refine (rcomputable.evaln_w rcomputable.snd hf
      (hc.comp rcomputable.fst) (hn.comp rcomputable.fst)) },
  exact (this.of_eq $ λ a, by simp [p, eval_eq_rfind])
end

theorem rpartrec.eval_s {f : α → ℕ → option ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hf : f computable₂_in o) (hc : c computable_in o) (hn : n computable_in o) :
  (λ x, code.eval (f x) (c x) (n x)) partrec_in o :=
begin 
  let p := (λ x, nat.rfind_opt (λ s, code.evaln s (f x) (c x) (n x))),
  have : p partrec_in o,
  { apply rpartrec.rfind_opt, 
    refine (rcomputable.evaln_s rcomputable.snd
      (rcomputable₂.comp₂ hf rcomputable.fst.to_unary₁ rcomputable.id'.to_unary₂)
      (hc.comp rcomputable.fst) (hn.comp rcomputable.fst)) },
  exact (this.of_eq $ λ a, by simp [p, eval_eq_rfind])
end

theorem rpartrec.eval_tot {f : ℕ → ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hf : f computable_in o) (hc : c computable_in o) (hn : n computable_in o) :
  (λ x, code.eval (↑ₒf) (c x) (n x)) partrec_in o :=
rpartrec.eval_w (rcomputable.option_some_iff.mpr hf) hc hn

theorem rpartrec.eval_tot_s {f : α → ℕ → ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hf : f computable₂_in o) (hc : c computable_in o) (hn : n computable_in o) :
  (λ x, code.eval (↑ₒ(f x)) (c x) (n x)) partrec_in o :=
rpartrec.eval_s (rcomputable.option_some_iff.mpr hf) hc hn

theorem rcomputable.univn_w (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {p : β → option τ} {s : γ → ℕ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hp : p computable_in o) (hs : s computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧*p [s x] (n x) : γ → option σ) computable_in o :=
begin
  simp [univn],
  refine rcomputable.option_bind (rcomputable.evaln_w hs
    (rcomputable.option_bind primrec.decode.to_rcomp _)
    ((primrec.of_nat _).to_rcomp.comp hi)
    (primrec.encode.to_rcomp.comp hn)) _,
  { refine rcomputable.option_map _ _,
    { exact hp.comp rcomputable.snd },
    { exact (primrec.encode.comp snd).to_rcomp } },
  { exact (primrec.decode.comp snd).to_rcomp }
end

theorem rpartrec.univ_w (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {p : β → option τ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hp : p computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧*p (n x) : γ →. σ) partrec_in o :=
begin
  simp [univ],
  refine rpartrec.bind (rpartrec.eval_w
    (rcomputable.option_bind primrec.decode.to_rcomp _)
    ((primrec.of_nat _).to_rcomp.comp hi)
    (primrec.encode.to_rcomp.comp hn)) _,
  { refine rcomputable.option_map (hp.comp rcomputable.snd) _,
    refine (primrec.encode.comp snd).to_rcomp },
  { refine (primrec.decode.comp snd).to_comp.of_option.to_rpart }
end

@[rcomputability]
theorem rcomputable.univn_tot (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {f : β → τ} {s : γ → ℕ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hf : f computable_in o) (hs : s computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧^f [s x] (n x) : γ → option σ) computable_in o :=
rcomputable.univn_w _ _ hi (rcomputable.option_some_iff.mpr hf) hs hn

@[rcomputability]
theorem rpartrec.univ_tot (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {f : β → τ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hf : f computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧^f (n x) : γ →. σ) partrec_in o :=
rpartrec.univ_w _ _ hi (rcomputable.option_some_iff.mpr hf) hn

theorem rcomputable.univn_s (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {p : γ → β → option τ} {s : γ → ℕ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hp : p computable₂_in o) (hs : s computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧*(p x) [s x] (n x) : γ → option σ) computable_in o :=
rcomputable.option_bind (rcomputable.evaln_s hs
  (rcomputable.option_bind (rcomputable.decode.to_unary₂)
    ((rcomputable.id'.option_map rcomputable.encode.to_unary₂).comp₂
      (rcomputable₂.comp₂ hp rcomputable.fst.to_unary₁ rcomputable.id'.to_unary₂)))
  ((primrec.of_nat _).to_rcomp.comp hi)
  (primrec.encode.to_rcomp.comp hn)) (rcomputable.decode.to_unary₂)

theorem rpartrec.univ_s (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {p : γ → β → option τ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hp : p computable₂_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧*(p x) (n x) : γ →. σ) partrec_in o :=
rpartrec.bind (rpartrec.eval_s
  (rcomputable.option_bind (rcomputable.decode.to_unary₂)
    ((rcomputable.id'.option_map rcomputable.encode.to_unary₂).comp₂
      (rcomputable₂.comp₂ hp rcomputable.fst.to_unary₁ rcomputable.id'.to_unary₂)))
  ((primrec.of_nat _).to_rcomp.comp hi)
    (primrec.encode.to_rcomp.comp hn)) ((rpartrec.coe.comp rcomputable.decode).to_unary₂)

@[rcomputability]
theorem rcomputable.univn_tot_s (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {f : γ → β → τ} {s : γ → ℕ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hf : f computable₂_in o) (hs : s computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧^(f x) [s x] (n x) : γ → option σ) computable_in o :=
rcomputable.univn_s _ _ hi (rcomputable.option_some_iff.mpr hf) hs hn

@[rcomputability]
theorem rpartrec.univ_tot_s (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {f : γ → β → τ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hf : f computable₂_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧^(f x) (n x) : γ →. σ) partrec_in o :=
rpartrec.univ_s _ _ hi (rcomputable.option_some_iff.mpr hf) hn

theorem rpartrec.exists_index {f : α →. σ} {g : β → τ} :
  f partrec_in! g ↔ ∃ e, ⟦e⟧^g = f :=
begin
  split,
  { let g' := (λ n, (decode β n).bind (λ a, some $ encode (g a))),
    have : (λ (n : ℕ), (of_option (decode β n)).bind (λ (a : β), some (encode (g a)))) = ↑ʳg',
    { funext n, simp [g'], cases decode β n; simp [of_option] },
    simp[univ, rpartrec_tot, rpartrec, nat.rpartrec.reducible], unfold_coes, rw this,
    assume h, rcases code.exists_code_opt.mp h with ⟨c, eqn_c⟩,
      refine ⟨encode c, funext $ λ a, _⟩, simp [eqn_c, part.of_option] },
  { rintros ⟨e, rfl⟩, refine rpartrec.univ_tot _ _
      (primrec.const e).to_rcomp rcomputable.refl rcomputable.id }
end

@[rcomputability]
theorem univ_partrec_in {f : α → σ} {e} :
  (⟦e⟧^f : β →. τ) partrec_in! f :=
rpartrec.univ_tot _ _ (primrec.const e).to_rcomp rcomputable.refl rcomputable.id

namespace rpartrec

section

lemma in_complement (p : α →. β) [∀ a, decidable (p a).dom] : p partrec_in! p.complement :=
(rpartrec.coe.comp rpartrec.refl).of_eq (λ a, by simp)

end

@[rcomputability]
protected theorem cond {c : α → bool} {f : α →. σ} {g : α →. σ} {h : β → τ}
  (hc : c computable_in! h) (hf : f partrec_in! h) (hg : g partrec_in! h) :
  (λ a, cond (c a) (f a) (g a)) partrec_in! h :=
begin
  rcases exists_index.1 hf with ⟨e, eqn_e⟩,
  rcases exists_index.1 hg with ⟨i, eqn_i⟩,
  have := rpartrec.univ_tot α σ (rcomputable.cond hc (rcomputable.const e) (rcomputable.const i))
    rcomputable.refl rcomputable.id,
  exact (this.of_eq $ λ a, by cases eqn : c a; simp[eqn, eqn_e, eqn_i])
end

theorem bool_to_part (c : α → bool):
  (λ a, cond (c a) (some 0) part.none : α →. ℕ) partrec_in (c : α →. bool) :=
rpartrec.cond rcomputable.refl (rcomputable.const 0) partrec.none.to_rpart

theorem universal_index {f : β → τ} : ∃ u, ∀ (x : ℕ) (y : α),
  (⟦u⟧^f (x, y) : part σ) = ⟦x⟧^f y :=
by rcases exists_index.mp 
   (rpartrec.univ_tot α σ rcomputable.fst (rcomputable.refl_in f) rcomputable.snd) with ⟨u, hu⟩;
   exact ⟨u, by simp[hu]⟩

theorem recursion (α σ) [primcodable α] [primcodable σ] (f : β → τ) :
  ∃ fixpoint : ℕ → ℕ, primrec fixpoint ∧
  ∀ {I : ℕ → ℕ} {i}, ⟦i⟧^f = ↑ᵣI →
    (⟦fixpoint i⟧^f : α →. σ) = ⟦I (fixpoint i)⟧^f :=
begin
  have : ∃ j, (⟦j⟧^f : ℕ × α →. σ) = λ a, (⟦a.1⟧^f a.1).bind (λ n : ℕ, ⟦n⟧^f a.2),
  { have this := (rpartrec.univ_tot ℕ ℕ rcomputable.fst rcomputable.refl rcomputable.fst).bind
      ((rpartrec.univ_tot α σ rcomputable.snd rcomputable.refl (snd.comp fst).to_rcomp)).to₂,
    exact exists_index.mp this },
  rcases this with ⟨j, lmm_j⟩,
  have : ∃ k, ⟦k⟧^f = λ (a : ℕ × ℕ), ⟦a.1⟧^f (curry j a.2),
  { have := rpartrec.curry_prim.to_comp.comp (computable.const j) computable.id,
    have := (rpartrec.univ_tot ℕ ℕ rcomputable.fst rcomputable.refl 
      (this.to_rcomp.comp rcomputable.snd)),
    exact exists_index.mp this },
  rcases this with ⟨k, lmm_k⟩,
  let fixpoint : ℕ → ℕ := λ x, curry j (curry k x),
  have : primrec fixpoint := rpartrec.curry_prim.comp (primrec.const j)
    (rpartrec.curry_prim.comp (primrec.const k) primrec.id),
  refine ⟨fixpoint, this, _⟩,
  assume I i h, funext x,
  show ⟦fixpoint i⟧^f x = ⟦I (fixpoint i)⟧^f x,
  simp[fixpoint, lmm_j, lmm_k, h],
end

theorem recursion1 (α σ) [primcodable α] [primcodable σ]
  {f : β → τ} {I : ℕ → ℕ} (h : I computable_in ↑ᵣf) :
  ∃ n, (⟦n⟧^f : α →. σ) = ⟦I n⟧^f :=
by rcases recursion α σ f with ⟨fixpoint, cf, hfix⟩;
   rcases exists_index.mp h with ⟨i, hi⟩;
   exact ⟨fixpoint i, hfix hi⟩

end rpartrec

noncomputable def bounded_computation (f : α →. σ) (h : β → τ) (s : ℕ) : α → option σ :=
⟦classical.epsilon (λ e : ℕ, ⟦e⟧^h = f)⟧^h [s]

notation f`^`h` .[`s`]` := bounded_computation f h s
  
theorem bounded_computation_spec {f : α →. σ} {h : β → τ} (hf : f partrec_in! h)
  {x y} : y ∈ f x ↔ ∃ s, f^h.[s] x = some y :=
begin
  have : y ∈ ⟦classical.epsilon (λ (y : ℕ), ⟦y⟧^h = f)⟧^h x ↔
    ∃ (s : ℕ), ⟦classical.epsilon (λ e, ⟦e⟧^h = f)⟧^h [s] x = some y,
  from rpartrec.univn_complete,
  have eqn := classical.epsilon_spec (rpartrec.exists_index.mp hf), simp[eqn] at this,
  exact this
end

def usen_pfun (σ) [primcodable σ] (p : β → option τ) (e : ℕ) (s : ℕ) (x : α) : part (option ℕ) :=
cond ((⟦e⟧*p [s] x : option σ)).is_some
  ((nat.rfind $ λ u : ℕ, (⟦e⟧*p [u] x : option σ).is_some).map option.some)
  (some option.none)

lemma usen_pfun_defined {p : β → option τ} {e : ℕ} {s : ℕ} {x : α} :
  (usen_pfun σ p e s x).dom :=
begin
  simp [usen_pfun],
  cases C : (⟦e⟧*p [s] x).is_some; simp [C, part.dom],
  refine ⟨s, _⟩, simp[C, part.some]
end 

def usen (σ) [primcodable σ] (f : β → option τ) (e : ℕ) (s : ℕ) (x : α) : option ℕ :=
(usen_pfun σ f e s x).get usen_pfun_defined

def usen0 (σ) [primcodable σ] (e : ℕ) (s : ℕ) (x : α) : option ℕ := usen σ ↑ₒ(λ _, 0 : ℕ → ℕ) e s x

notation `Φ⟦` e `⟧^`f ` [` s `]`  := usen _ ↑ₒf e s

notation `Φ⟦` e `⟧⁰` ` [` s `]` := usen0 _ e s

@[rcomputability]
theorem rcomputable.usen_tot (σ) [primcodable σ]
  {f : β → τ} {i : γ → ℕ} {s : γ → ℕ} {a : γ → α} {o : μ → ν}
  (hf : f computable_in! o) (hi : i computable_in! o) (hs : s computable_in! o) (ha : a computable_in! o) :
  (λ x, usen σ ↑ₒf (i x) (s x) (a x)) computable_in! o :=
begin
  suffices :
    (λ x, usen_pfun σ ↑ₒf (i x) (s x) (a x)) partrec_in! o,
  from (this.of_eq $ λ n, by simp [usen]),
  refine rpartrec.cond _ _ _,
  { refine primrec.option_is_some.to_rcomp.comp (rcomputable.univn_tot _ _ hi hf hs ha) },
  { refine (rpartrec.rfind _).map _,
    { refine primrec.option_is_some.to_rcomp.comp
      (rcomputable.univn_tot _ _ (hi.comp rcomputable.fst) hf rcomputable.snd (ha.comp rcomputable.fst)) },
    { refine (primrec.succ.comp snd).to_rcomp } },
  { refine rcomputable.const _ }
end

@[rcomputability]
theorem computable.usen_to_fn (σ) [primcodable σ] {β} [decidable_eq β] [denumerable β]
  {l : γ → list (β × τ)} {i : γ → ℕ} {s : γ → ℕ} {a : γ → α} {o : μ → ν}
  (hl : computable l) (hi : computable i) (hs : computable s) (ha : computable a) :
  computable (λ x, usen σ (l x).to_fn (i x) (s x) (a x)) :=
begin
  suffices :
    partrec (λ x, usen_pfun σ (l x).to_fn (i x) (s x) (a x)),
  from (this.of_eq $ λ n, by simp [usen] ),
  refine partrec.cond _ _ _,
  { refine (option_is_some.to_comp.comp (computable.univn_to_fn α σ hi hl hs ha))},
  { refine (partrec.rfind _).map _,
    { refine primrec.option_is_some.to_comp.comp
        (computable.univn_to_fn _ _ (hi.comp computable.fst) (hl.comp computable.fst)
        computable.snd (ha.comp computable.fst)) },
    refine (primrec.succ.to_comp.comp computable.snd) },
  { refine (const _).to_comp }
end

theorem usen_eq_tt {p : β → option τ} {e : ℕ} {s : ℕ} {x : α}
  (h : (⟦e⟧*p [s] x : option σ).is_some = tt) :
  usen σ p e s x = ((nat.rfind (λ u, (⟦e⟧*p [u] x).is_some)).get (rfind_dom_total ⟨s, h⟩)) :=
by simp [usen, usen_pfun, h, map]

theorem usen_eq_ff {p : β → option τ} {e : ℕ} {s : ℕ} {x : α}
  (h : (⟦e⟧*p [s] x : option σ).is_some = ff) :
  usen σ p e s x = none :=
by simp [usen, usen_pfun, h, map]

theorem usen_is_some_iff {p : β → option τ} {e : ℕ} {s : ℕ} {x : α} :
  (usen σ p e s x).is_some ↔ (⟦e⟧*p [s] x : option σ).is_some :=
by { cases C : (⟦e⟧*p [s] x).is_some, { simp[usen_eq_ff C] }, { simp[usen_eq_tt C] } }

theorem usen_step_tt {p : β → option τ} {e : ℕ} {s : ℕ}  {x : α}
  {u : ℕ} (hu : usen σ p e s x = u) :
  (⟦e⟧*p [u] x : option σ).is_some = tt :=
begin
  have : (⟦e⟧*p [s] x : option σ).is_some, { simp[←usen_is_some_iff, hu] },
  simp [usen_eq_tt this] at hu,
  have : u ∈ nat.rfind (λ u, (⟦e⟧*p [u] x).is_some), rw ←hu, from get_mem _,
  simp at this, simp [this.1]
end

theorem usen_consumption_step {p : ℕ → option τ} {e : ℕ} {s : ℕ} {x : α} {y : σ}
  {u : ℕ} (hu : usen σ p e s x = u) :
  ⟦e⟧*p [s] x = some y → ∀ {q : ℕ → option τ}, (∀ n, n < u → q n = p n) →
  ⟦e⟧*q [u] x = some y := λ h q hq,
begin
  suffices : (⟦e⟧*q [u] : α → option σ) = ⟦e⟧*p [u],
  { simp [this], have := usen_step_tt hu,
    rcases option.is_some_iff_exists.mp this with ⟨z, hz⟩,
    simp [rpartrec.univn_mono_eq h hz, hz] },
  apply rpartrec.univn_use, exact hq
end

theorem usen_le {p : β → option τ} {e : ℕ} {s : ℕ} {x : α}
  (u : ℕ) (hu : usen σ p e s x = u) : u ≤ s :=
begin
  cases h : (⟦e⟧*p [s] x : option σ).is_some,
  { exfalso, simp[usen_eq_ff h] at hu, contradiction },
  { simp [usen_eq_tt h] at hu, rcases hu with rfl,
    let u := (nat.rfind ↑(λ u, (⟦e⟧*p [u] x).is_some)).get (rfind_dom_total ⟨_, h⟩),
    suffices : u ≤ s, from this,
    have eqn : u ≤ s ∨ s < u, from le_or_lt u s, cases eqn, refine eqn,
    exfalso,
    have : u ∈ nat.rfind (λ u, (⟦e⟧*p [u] x).is_some), from get_mem _,
    simp at this,
    have := this.2 eqn, simp [h] at this, refine this }
end

def usen_mono {p : β → option τ} {e : ℕ} {x : α}
  {m n u : ℕ} (le : u ≤ n) (hm : usen σ p e m x = u) : usen σ p e n x = u :=
begin
  have mdom : (⟦e⟧*p [m] x : option σ).is_some, from usen_is_some_iff.mp (by simp[hm]),
  have udom : (⟦e⟧*p [u] x : option σ).is_some, from usen_step_tt hm,
  have ndom : (⟦e⟧*p [n] x : option σ).is_some, from rpartrec.univn_dom_mono le udom, 
  have : usen σ p e m x = (nat.rfind (λ u, (⟦e⟧*p [u] x).is_some)).get _, from usen_eq_tt mdom,
  have : usen σ p e n x = usen σ p e m x, simp[this], from usen_eq_tt ndom,
  simp[this, hm]
end

def use (σ) [primcodable σ] (p : β → option τ) (e : ℕ) (x : α) : part ℕ :=
nat.rfind_opt (λ s, usen σ p e s x)

@[rcomputability]
theorem rcomputable.use_tot (σ) [primcodable σ]
  {f : β → τ} {i : γ → ℕ} {s : γ → ℕ} {a : γ → α} {o : μ → τ}
  (hf : f computable_in! o) (hi : i computable_in! o) (hs : s computable_in! o) (ha : a computable_in! o) :
  (λ x, use σ ↑ₒf (i x) (a x)) partrec_in! o :=
rpartrec.rfind_opt
  (rcomputable.usen_tot _ hf (rcomputable.to_unary₁ hi)
    ((rpartrec.of_option' rcomputable.id').to_unary₂) (rcomputable.to_unary₁ ha))
  
def use0 (σ) [primcodable σ] (e : ℕ) (x : α) : part ℕ := use σ ↑ₒ(λ _, 0 : ℕ → ℕ) e x

notation `Φ⟦` e `⟧^`f  := use _ ↑ₒf e

notation `Φ⟦` e `⟧⁰ ` x := use0 _ e x

theorem use_dom_iff {p : β → option τ} {e : ℕ} {x : α} :
  (use σ p e x).dom ↔ (⟦e⟧*p x : part σ).dom :=
calc (use σ p e x).dom ↔ ∃ s, (usen σ p e s x).is_some         : by simp[use, nat.rfind_opt_dom, option.is_some_iff_exists]
                   ... ↔ ∃ s, (⟦e⟧*p [s] x : option σ).is_some : by simp[usen_is_some_iff]
                   ... ↔ (⟦e⟧*p x : part σ).dom                : iff.symm rpartrec.univn_dom_complete

theorem use_eq_iff {p : β → option τ} {e : ℕ} {x : α} {u : ℕ} :
  u ∈ use σ p e x ↔ usen σ p e u x = u :=
calc u ∈ use σ p e x ↔ ∃ s, usen σ p e s x = u : nat.rfind_opt_mono (λ u m n le h, usen_mono ((usen_le u h).trans le) h)
                 ... ↔ usen σ p e u x = u      : ⟨λ ⟨s, eq_use⟩, usen_mono (by refl) eq_use, λ h, ⟨u, h⟩⟩
