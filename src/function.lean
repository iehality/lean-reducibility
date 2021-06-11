import rpartrec coding

open encodable denumerable roption

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
  have c₁ : partrec (λ x, ↑(decode σ x.2) : α × ℕ →. σ) := computable.decode.of_option.comp computable.snd,
  exact ((c₀.bind (c₁.to_rpart)).of_eq $ λ a, by simp[encode2])
end

def graph {α β} [decidable_eq β] (f : α → β) : α × β → bool :=
λ x, to_bool (f x.1 = x.2)

def epsilon_r {β} [primcodable β] [inhabited β] (p : β →. bool) : roption β := 
  ((nat.rfind $ λ x, p ((decode β x).get_or_else (default β))).map 
    (λ x, (decode β x).get_or_else (default β)))

def epsilon {β} [primcodable β] [inhabited β] (p : β → bool) : roption β :=
epsilon_r (p : β →. bool)

theorem epsilon_witness {β} [primcodable β] [inhabited β] {p : β → bool} {b : β} :
  b ∈ epsilon p → p b = tt :=
by { simp[epsilon,epsilon_r], intros x h hl he, rw he at h, simp[←h] }

@[simp] theorem exists_epsilon_iff {β} [primcodable β] [inhabited β] {p : β → bool} :
  (epsilon p).dom ↔ (∃ b, p b = tt) := by { split,
{ intros w, use (epsilon p).get w, exact epsilon_witness ⟨w, rfl⟩ },
{ rintros ⟨b, hb⟩, simp[epsilon,epsilon_r, roption.map, roption.some],
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

lemma nat.initialpart_fdecode {α σ} [decidable_eq α] [denumerable α] {f : α → option σ} {s a b}
  (h : encode a < s) (hn : f a = some b) : (f↾s).fdecode a = some b :=
by simp; rw (show a = of_nat α (encode a), by simp) at hn ⊢; exact nat.initialpart_nth h hn

lemma nat.initialpart_fdecode_none {α σ} [decidable_eq α] [denumerable α] {f : α → option σ} {a}
  (ha : f a = none) (s) : (f↾s).fdecode a = none :=
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
        have l0 : ∀ (l : ℕ), m - i0.succ ≤ l → l < n → p l = ff,
        { intros l el0 el1, 
          have le : m - i0.succ = l ∨ m - i0 ≤ l, omega,
          cases le, simp[←ep, le],  exact h0 _ le el1 },
        exact ⟨show m - i0.succ ≤ n, by omega, e1, e2, l0⟩ },
      { rintros ⟨e0, e1, e2, h0⟩, split,
        { have l0 : m - i0.succ = n ∨ m - i0 ≤ n, omega, cases l0,
          { exfalso, simp[l0, e2] at ep, exact ep },
          { exact l0 } },
        { have l0 : ∀ (l : ℕ), m - i0 ≤ l → l < n → p l = ff := λ _ _ el1, h0 _ (by omega) el1,
          exact ⟨e1, e2, l0⟩ } } },
    { simp, split,
      { assume e, rw e at ep, simp[e],
        exact ⟨by refl, by omega, ep, by { intros m l0 l1, exfalso, exact nat.lt_le_antisymm l1 l0 }⟩ },
      { rintros ⟨e0, e1, e2, h0⟩,
        have l0 : m - i0.succ < n ∨ m - i0.succ = n, omega,
        cases l0,
        { exfalso, have c : p (m - i0.succ) = ff , exact h0 _ (by refl) l0,
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

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

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

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem epsilon_r_rpartrec [inhabited β] (p : α × β →. bool) :
  (λ a, epsilon_r (λ x, p (a, x))) partrec_in p :=
begin
  have c₀ : (λ x, p (x.1, (decode β x.2).get_or_else (default β)) : α × ℕ →. bool) partrec_in p :=
  (rpartrec.refl.comp $ (computable.pair computable.fst 
    ((computable.decode.comp computable.snd).option_get_or_else (computable.const (default β))))
    .to_rpart),
  have c₁ : computable (λ x, (decode β x.2).get_or_else (default β) : α × ℕ → β) :=
  (computable.decode.comp computable.snd).option_get_or_else (computable.const (default β)),
  have c₂ : (λ a, nat.rfind $ λ x, p (a, (decode β x).get_or_else (default β))) partrec_in p :=
  rpartrec.rfind.trans c₀,
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
  have c₂ : (λ a, nat.rfind $ λ x, p a ((decode β x).get_or_else (default β))) partrec_in prod.unpaired p :=
  rpartrec.rfind.trans c₀,
  exact c₂.map c₁.to_rpart
end

protected theorem epsilon_r [inhabited β] {p : α → β →. bool} {g : γ →. σ}
  (hp : prod.unpaired p partrec_in g) : (λ a, epsilon_r (p a)) partrec_in g :=
epsilon_r_rpartrec_refl.trans hp

protected theorem epsilon [inhabited β] {p : α → β → bool} {g : γ →. σ}
  (hp : prod.unpaired p computable_in g) :
  (λ a, epsilon (p a)) partrec_in g :=
epsilon_r_rpartrec_refl.trans hp

theorem epsilon_rpartrec [inhabited β] (p : α × β → bool) :
  (λ a, epsilon (λ x, p (a, x))) partrec_in (λ x, some $ p x) :=
epsilon_r_rpartrec _  

end rpartrec

namespace rcomputable

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

protected theorem epsilon [inhabited β] {p : α → β → bool} {g : γ →. σ}  :
  prod.unpaired p computable_in g → (λ a, epsilon (p a)) partrec_in g := λ cp,
rpartrec.epsilon_r cp

theorem initialpart {α} [denumerable α] {f : α → option σ} {g : β →. τ}
  (hf : f computable_in g) : (↾) f computable_in g :=
begin
  let I : ℕ → list (α × σ) := (λ n : ℕ, n.elim []
    (λ m IH, option.cases_on (f (of_nat α m)) IH (λ a, (of_nat α m, a) :: IH))),
  have : I computable_in g,
  { refine rcomputable.nat_elim'
      rcomputable.id
      (rcomputable.const _) _, simp,
    refine rcomputable.option_cases'
      (hf.comp ((primrec.of_nat _).to_rcomp.comp $ fst.comp snd))
      (snd.comp snd) _, simp,
    refine (primrec.list_cons.comp (((primrec.of_nat _).comp $ primrec.fst.comp $
      primrec.snd.comp primrec.fst).pair primrec.snd) $ primrec.snd.comp $
      primrec.snd.comp primrec.fst).to_rcomp },
  exact (this.of_eq $ λ n, by induction n with n IH; simp[I]; simp[←IH])
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

theorem foldr [inhabited α] (f : α × β → β) :
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
(foldr f).comp (pair (const b) id)

theorem graph_rcomp [decidable_eq β] (f : α → β)  : graph f computable_in (f : α →. β) :=
  have c₀ : (λ x, to_bool (x.1 = x.2) : β × β → bool) computable_in (f : α →. β) := primrec.eq.to_rcomp,
  have c₂ : (λ x, (f x.1, x.2) : α × β → β × β) computable_in (f : α →. β) := rcomputable.pair 
  (rcomputable.refl.comp rcomputable.fst) rcomputable.snd,
c₀.comp c₂

theorem subseq_rcomputable [decidable_eq α] [inhabited α] (f : ℕ → α) :
  list.subseq f computable_in (f : ℕ →. α) :=
begin
  let g := (λ x, (x.2.1 + 1, x.2.2 && graph f (x.2.1, x.1)) : α × ℕ × bool → ℕ × bool),
  let subseq0 := (λ x, (list.foldr (λ y z, g (y, z)) (0, tt) x) : list α → ℕ × bool),
  let subseq1 := (λ x, (subseq0 x).2),
  have cg : g computable_in (f : ℕ →. α) := ((computable.succ.to_rcomp).comp (fst.comp snd)).pair 
  (((primrec.dom_bool₂ band).to_rcomp).comp $
    (snd.comp snd).pair $
      (rcomputable.graph_rcomp f).comp ((fst.comp snd).pair fst)),
  have cic : subseq1 computable_in (f : ℕ →. α) := rcomputable.snd.comp ((rcomputable.foldr0 g (0, tt)).trans cg),
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
      (hp.comp (fst.pair (primrec.nat_sub.to_comp.to_rcomp.comp $
        (hf.comp fst).pair (computable.succ.to_rcomp.comp $ fst.comp snd))))
        (primrec.option_some.to_rcomp.comp (primrec.nat_sub.to_comp.to_rcomp.comp $
        (hf.comp fst).pair (computable.succ.to_rcomp.comp $ fst.comp snd))) (snd.comp snd) },
  have e : ∀ a b n, nat.elim option.none (λ y IH, cond (p a (b - y.succ)) (some $ b - y.succ) IH) n = 
    nat.rfind_fin0 (p a) b n,
  { intros a b n, simp, induction n with n0 ih; simp[nat.rfind_fin0], rw ih },
  have c₂ := nat_elim hg (const option.none) c₁,
  exact (c₂.of_eq $ λ n, by simp[f₁]; simp; rw e)
end

theorem rfind_fin {p : α → ℕ → bool} {f : α → ℕ} {g : β →. τ}
  (hp : prod.unpaired p computable_in g) (hf : f computable_in g) :
  (λ a, nat.rfind_fin (p a) (f a)) computable_in g := 
rfind_fin0 hp hf hf

end rcomputable

open nat.rpartrec primrec

-- !!!! AXIOM !!!!
axiom primrec.evaln_fdecode :
  primrec (λ x : ℕ × list (ℕ × ℕ) × code × ℕ, code.evaln x.1 x.2.1.fdecode x.2.2.1 x.2.2.2)

variables {α : Type*} {σ : Type*} {β : Type*} {τ : Type*} {γ : Type*} {μ : Type*} {ν : Type*}
variables [primcodable α] [primcodable σ] [primcodable β] [primcodable τ] [primcodable γ] [primcodable μ] [primcodable ν]

theorem computable.evaln_fdecode
  {s : α → ℕ} {l : α → list (ℕ × ℕ)} {c : α → code} {n : α → ℕ}
  (hs : computable s) (hl : computable l) (hc : computable c) (hn : computable n) :
  computable (λ x, code.evaln (s x) (l x).fdecode (c x) (n x)) :=
primrec.evaln_fdecode.to_comp.comp (hs.pair $ hl.pair $ hc.pair hn)

theorem eval_eq_rfind (f : ℕ → option ℕ) (c n) :
  code.eval f c n = nat.rfind_opt (λ s, code.evaln s f c n) :=
roption.ext $ λ x, begin
  refine code.evaln_complete.trans (nat.rfind_opt_mono _).symm,
  intros a m n hl, apply code.evaln_mono hl,
end

theorem partrec.eval_fdecode {α} [primcodable α]
  {l : α → list (ℕ × ℕ)} {c : α → code} {n : α → ℕ}
  (hl : computable l) (hc : computable c) (hn : computable n) :
  partrec (λ x, code.eval (l x).fdecode (c x) (n x)) :=
begin
  let f := (λ x, nat.rfind_opt (λ s, code.evaln s (l x).fdecode (c x) (n x))),
  have : partrec f := (partrec.rfind_opt $
    computable.evaln_fdecode computable.snd
    (hl.comp computable.fst) (hc.comp computable.fst) (hn.comp computable.fst)),
  exact (this.of_eq $ by simp[f, eval_eq_rfind])
end

theorem list.fdecode_map [decidable_eq σ] [denumerable σ]
  (f : τ → option μ) (c : list (σ × τ)) (n) :
  (c.fdecode n).map f = (c.map (λ x : σ × τ, (x.1, f x.2))).fdecode n :=
begin
  cases C : c.fdecode n with v; simp; symmetry,
  { simp [list.fdecode_iff_none] at C ⊢, intros m o x y eqn_xy eqn_n,
    have := C m y, simp [eqn_n] at eqn_xy, contradiction },
  { simp [list.fdecode_iff] at C ⊢, rcases C with ⟨m, eqn_nv, hyp⟩,
    refine ⟨m, ⟨n, v, eqn_nv, rfl, rfl⟩, λ k p eqn_k x y eqn_xy eqn_n eqn_p, _⟩,
    have := hyp _ y eqn_k, rw [eqn_n] at eqn_xy, contradiction }
end

theorem list.fdecode_encode_of_nat {σ} [decidable_eq σ] [denumerable σ]
  (c : list (σ × τ)) :
  (λ n, option.map encode (c.fdecode (of_nat σ n))) = 
  (c.map (λ x : σ × τ, (encode x.1, encode x.2))).fdecode :=
begin
  funext n,
  cases C : c.fdecode (of_nat σ n) with v; simp; symmetry,
  { simp [list.fdecode_iff_none] at C ⊢, intros m k x y eqn_xy eqn_n eqn_k,
    have := C m y, rw ←eqn_n at this, simp at this, contradiction },
  { simp [list.fdecode_iff] at C ⊢, rcases C with ⟨m, eqn_nv, hyp⟩,
    refine ⟨m, ⟨_, _, eqn_nv, (by simp), rfl⟩, λ k z eqn_k x y eqn_xy eqn_n eqn_z, _⟩,
    have := hyp _ y eqn_k, rw ←eqn_n at this, simp at this, contradiction }
end

theorem computable.univn_fdecode (α σ) [primcodable α] [primcodable σ] {β} [decidable_eq β] [denumerable β]
  {i : γ → ℕ} {l : γ → list (β × τ)} {s : γ → ℕ} {n : γ → α}
  (hi : computable i) (hl : computable l) (hs : computable s) (hn : computable n) :
  computable (λ x : γ, (⟦i x⟧*(l x).fdecode [s x] (n x) : option σ)) :=
begin
  simp [univn, list.fdecode_encode_of_nat],
  refine computable.option_bind (computable.evaln_fdecode hs
    ((list_map primrec.id ((primrec.encode.comp $ fst.comp snd).pair
      (primrec.encode.comp $ snd.comp snd)).to₂).to_comp.comp hl)
    ((primrec.of_nat _).to_comp.comp hi)
    (primrec.encode.to_comp.comp hn))
    (primrec.decode.comp snd).to_comp
end

theorem partrec.univ_fdecode (α σ) [primcodable α] [decidable_eq σ] [denumerable σ]
  {i : γ → ℕ} {l : γ → list (σ × τ)} {n : γ → α}
  (hi : computable i) (hl : computable l) (hn : computable n) :
  partrec (λ x : γ, (⟦i x⟧*(l x).fdecode (n x) : roption σ)) :=
begin
  simp [univ, list.fdecode_encode_of_nat],
  refine partrec.bind (partrec.eval_fdecode
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
  let u := (λ x, code.evaln (s x) (f↾(s x)).fdecode (c x) (n x)),
  have eqn_u : (λ x, code.evaln (s x) f (c x) (n x)) = u,
  { suffices :
      ∀ t d, code.evaln t (f↾t).fdecode d = code.evaln t f d,
    { funext, simp[u] at this ⊢, rw this },
    intros t d,
    apply code.evaln_use,
    intros u eqn_u,
    { cases C : f u,
      { exact nat.initialpart_fdecode_none C t },
      { exact nat.initialpart_fdecode (show encode u < t, from eqn_u) C } } },
  rw eqn_u,
  simp only [u],
  let m := (λ x, (s x, f↾s x, c x, n x)),
  have lmm_m : m computable_in o := (hs.pair $
    (((rcomputable.initialpart rcomputable.refl).trans hf).comp hs).pair $ hc.pair hn),
  have := computable.evaln_fdecode fst.to_comp (fst.comp snd).to_comp
    (fst.comp $ snd.comp snd).to_comp (snd.comp $ snd.comp snd).to_comp,
  have := this.to_rcomp.comp lmm_m,
  exact this
end

theorem rcomputable.evaln_tot {s : α → ℕ} {f : ℕ → ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hs : s computable_in o) (hf : f computable_in o) (hc : c computable_in o) (hn : n computable_in o) : 
  (λ x, code.evaln (s x) ↑ₒf (c x) (n x)) computable_in o := 
rcomputable.evaln_w hs (rcomputable.option_some_iff.mpr hf) hc hn

theorem rpartrec.eval_w {f : ℕ → option ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hf : f computable_in o) (hc : c computable_in o) (hn : n computable_in o) :
  (λ x, code.eval f (c x) (n x)) partrec_in o :=
begin
  let p := (λ x, nat.rfind_opt (λ s, code.evaln s f (c x) (n x))),
  have : p partrec_in o,
  { apply rpartrec.rfind_opt', simp,
    refine (rcomputable.evaln_w rcomputable.snd hf
      (hc.comp rcomputable.fst) (hn.comp rcomputable.fst)) },
  exact (this.of_eq $ λ a, by simp [p, eval_eq_rfind])
end

theorem rpartrec.eval_tot {f : ℕ → ℕ} {c : α → code} {n : α → ℕ} {o : β →. σ}
  (hf : f computable_in o) (hc : c computable_in o) (hn : n computable_in o) :
  (λ x, code.eval (↑ₒf) (c x) (n x)) partrec_in o :=
rpartrec.eval_w (rcomputable.option_some_iff.mpr hf) hc hn

theorem rcomputable.univn_w (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {p : β → option τ} {s : γ → ℕ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hp : p computable_in o) (hs : s computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧*p [s x] (n x) : γ → option σ) computable_in o :=
begin
  simp [univn],
  refine rcomputable.option_bind' (rcomputable.evaln_w hs
    (rcomputable.option_bind' primrec.decode.to_rcomp _)
    ((primrec.of_nat _).to_rcomp.comp hi)
    (primrec.encode.to_rcomp.comp hn)) _,
  { simp, refine rcomputable.option_map' _ _,
    { exact hp.comp rcomputable.snd },
    { simp, exact (primrec.encode.comp snd).to_rcomp } },
  { simp, exact (primrec.decode.comp snd).to_rcomp }
end

theorem rpartrec.univ_w (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {p : β → option τ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hp : p computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧*p (n x) : γ →. σ) partrec_in o :=
begin
  simp [univ],
  refine rpartrec.bind' (rpartrec.eval_w
    (rcomputable.option_bind' primrec.decode.to_rcomp _)
    ((primrec.of_nat _).to_rcomp.comp hi)
    (primrec.encode.to_rcomp.comp hn)) _,
  { simp, refine rcomputable.option_map' (hp.comp rcomputable.snd) _,
    simp, refine (primrec.encode.comp snd).to_rcomp },
  { simp, refine (primrec.decode.comp snd).to_comp.of_option.to_rpart }
end

theorem rcomputable.univn_tot (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {f : β → τ} {s : γ → ℕ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hf : f computable_in o) (hs : s computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧^f [s x] (n x) : γ → option σ) computable_in o :=
rcomputable.univn_w _ _ hi (rcomputable.option_some_iff.mpr hf) hs hn

theorem rpartrec.univ_tot (α σ) [primcodable α] [primcodable σ]
  {i : γ → ℕ} {f : β → τ} {n : γ → α} {o : μ →. ν}
  (hi : i computable_in o) (hf : f computable_in o) (hn : n computable_in o) :
  (λ x, ⟦i x⟧^f (n x) : γ →. σ) partrec_in o :=
rpartrec.univ_w _ _ hi (rcomputable.option_some_iff.mpr hf) hn

theorem rpartrec.exists_index {f : α →. σ} {g : β → τ} :
  f partrec_in! g ↔ ∃ e, ⟦e⟧^g = f :=
begin
  split,
  { let g' := (λ n, (decode β n).bind (λ a, some $ encode (g a))),
    have : (λ (n : ℕ), (of_option (decode β n)).bind (λ (a : β), some (encode (g a)))) = ↑ʳg',
    { funext n, simp [g'], cases decode β n; simp [of_option] },
    simp[univ, rpartrec_tot, rpartrec, nat.rpartrec.reducible], unfold_coes, rw this,
    assume h, rcases code.exists_code_opt.mp h with ⟨c, eqn_c⟩,
      refine ⟨encode c, funext $ λ a, _⟩, simp [eqn_c, roption.of_option] },
  { rintros ⟨e, rfl⟩, refine rpartrec.univ_tot _ _
      (primrec.const e).to_rcomp rcomputable.refl rcomputable.id }
end

namespace rpartrec

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

theorem bool_to_roption (c : α → bool):
  (λ a, cond (c a) (some 0) roption.none : α →. ℕ) partrec_in (c : α →. bool) :=
rpartrec.cond rcomputable.refl (rcomputable.const 0) partrec.none.to_rpart

theorem universal_index {f : β → τ} : ∃ u, ∀ (x : ℕ) (y : α),
  (⟦u⟧^f (x, y) : roption σ) = ⟦x⟧^f y :=
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
      ((rpartrec.univ_tot α σ rcomputable.snd rcomputable.refl (snd.comp fst).to_rcomp)),
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

def use_pfun (σ) [primcodable σ] (p : β → option τ) (e : ℕ) (s : ℕ) (x : α) : roption ℕ :=
cond ((⟦e⟧*p [s] x : option σ)).is_some
  ((nat.rfind $ λ u : ℕ, (⟦e⟧*p [u] x : option σ).is_some).map nat.succ)
  (some 0)

lemma use_pfun_defined {p : β → option τ} {e : ℕ} {s : ℕ} {x : α} :
  (use_pfun σ p e s x).dom :=
begin
  simp [use_pfun],
  cases C : (⟦e⟧*p [s] x).is_some; simp [C],
  suffices : (nat.rfind (λ u, (⟦e⟧*p [u] x).is_some)).dom,
  { rcases roption.dom_iff_mem.mp this with ⟨_, h⟩,
    rw roption.eq_some_iff.mpr h, simp },
  refine rfind_dom_total ⟨s, C⟩
end 

def use (σ) [primcodable σ] (f : β → option τ) (e : ℕ) (s : ℕ) (x : α) : ℕ :=
(use_pfun σ f e s x).get use_pfun_defined

notation `useᵪ` := use bool
notation `useₙ` := use ℕ

theorem rcomputable.use_tot (σ) [primcodable σ]
  {f : β → τ} {i : γ → ℕ} {s : γ → ℕ} {a : γ → α} {o : μ → τ}
  (hf : f computable_in! o) (hi : i computable_in! o) (hs : s computable_in! o) (ha : a computable_in! o) :
  (λ x, use σ ↑ₒf (i x) (s x) (a x)) computable_in! o :=
begin
  suffices :
    (λ x, use_pfun σ ↑ₒf (i x) (s x) (a x)) partrec_in! o,
  from (this.of_eq $ λ n, by simp [use]),
  refine rpartrec.cond _ _ _,
  { refine primrec.option_is_some.to_rcomp.comp (rcomputable.univn_tot _ _ hi hf hs ha) },
  { refine (rpartrec.rfind' _).map' _; simp,
    { refine primrec.option_is_some.to_rcomp.comp
      (rcomputable.univn_tot _ _ (hi.comp rcomputable.fst) hf rcomputable.snd (ha.comp rcomputable.fst)) },
    { refine (primrec.succ.comp snd).to_rcomp } },
  { refine rcomputable.const _ }
end

theorem computable.use_fdecode (σ) [primcodable σ] {β} [decidable_eq β] [denumerable β]
  {l : γ → list (β × τ)} {i : γ → ℕ} {s : γ → ℕ} {a : γ → α} {o : μ → ν}
  (hl : computable l) (hi : computable i) (hs : computable s) (ha : computable a) :
  computable (λ x, use σ (l x).fdecode (i x) (s x) (a x)) :=
begin
  suffices :
    partrec (λ x, use_pfun σ (l x).fdecode (i x) (s x) (a x)),
  from (this.of_eq $ λ n, by simp [use] ),
  refine partrec.cond _ _ _,
  { refine (option_is_some.to_comp.comp (computable.univn_fdecode α σ hi hl hs ha))},
  { refine (partrec.rfind _).map _,
    { refine primrec.option_is_some.to_comp.comp
        (computable.univn_fdecode _ _ (hi.comp computable.fst) (hl.comp computable.fst)
        computable.snd (ha.comp computable.fst)) },
    refine (primrec.succ.to_comp.comp computable.snd) },
  { refine (const _).to_comp }
end

theorem use_eq_tt {p : β → option τ} {e : ℕ} {s : ℕ} {x : α}
  (h : (⟦e⟧*p [s] x : option σ).is_some = tt) :
  use σ p e s x = ((nat.rfind (λ u, (⟦e⟧*p [u] x).is_some)).get (rfind_dom_total ⟨_, h⟩)) + 1 :=
by simp [use, use_pfun, h, map]

theorem use_eq_ff {p : β → option τ} {e : ℕ} {s : ℕ} {x : α}
  (h : (⟦e⟧*p [s] x : option σ).is_some = ff) :
  use σ p e s x = 0 :=
by simp [use, use_pfun, h, map]

theorem use_step_tt {p : β → option τ} {e : ℕ} {s : ℕ}  {x : α}
  {u} (hu : u + 1 = use σ p e s x) (h : (⟦e⟧*p [s] x : option σ).is_some = tt) :
  (⟦e⟧*p [u] x : option σ).is_some = tt :=
begin
  simp [use_eq_tt h] at hu,
  have : u ∈ nat.rfind (λ u, (⟦e⟧*p [u] x).is_some), rw hu, from get_mem _,
  simp at this, simp [this.1]
end

theorem use_consumption_step {p : ℕ → option τ} {e : ℕ} {s : ℕ} {x : α} {y : σ}
  {u} (hu : u + 1 = use σ p e s x) :
  ⟦e⟧*p [s] x = some y → ∀ {q : ℕ → option τ}, (∀ n, n < u → q n = p n) → ⟦e⟧*q [u] x = some y := λ h q hq,
begin
  have h' := option.is_some_iff_exists.mpr ⟨_, h⟩,
  suffices :
    (⟦e⟧*q [u] : α → option σ) = ⟦e⟧*p [u],
  { simp [this], have := use_step_tt hu h',
    rcases option.is_some_iff_exists.mp this with ⟨z, hz⟩,
    simp [rpartrec.univn_mono_eq h hz, hz] },
  apply rpartrec.univn_use, exact hq,
end

theorem use_le {α σ} [primcodable α] [primcodable σ] {p : β → option τ} {e : ℕ} {s : ℕ} {x : α} :
  use σ p e s x ≤ s + 1 :=
begin
  cases h : (⟦e⟧*p [s] x : option σ).is_some,
  { simp [use_eq_ff h] },
  { simp [use_eq_tt h],
    let u := (nat.rfind ↑(λ u, (⟦e⟧*p [u] x).is_some)).get (rfind_dom_total ⟨_, h⟩),
    suffices : u ≤ s, from this,
    have eqn : u ≤ s ∨ s < u, from le_or_lt u s, cases eqn, refine eqn,
    exfalso,
    have : u ∈ nat.rfind (λ u, (⟦e⟧*p [u] x).is_some), from get_mem _,
    simp at this,
    have := this.2 eqn, simp [h] at this, refine this }
end

