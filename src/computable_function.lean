
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

@[simp] def nat.initial_code (f : ℕ → ℕ) : ℕ → list ℕ
| 0            := []
| (nat.succ n) := f n :: nat.initial_code n

def initial_code {α β} [encodable α] [encodable β] [inhabited α] (f : α → β) : ℕ → list ℕ :=
λ s, nat.initial_code (λ a, encode (f ((decode α a).get_or_else (default α)))) s

def list.rnth {α} (l : list α) := l.reverse.nth 

def graph {α β} (f : α → β) [∀ x y, decidable (@eq β x y)] : α × β → bool :=
λ x, to_bool (f x.1 = x.2)

theorem list.rnth_ext {α} {l₁ l₂ : list α} (h : ∀ n, l₁.rnth n = l₂.rnth n) : l₁ = l₂ :=
list.reverse_inj.mp (list.ext h)

lemma list.rnth_concat_length {α} (n : α) (l : list α) : (n :: l).rnth l.length = n :=
by { simp[list.rnth], 
     have : l.length = l.reverse.length, simp,
     simp only [this, list.nth_concat_length], refl }

def list.subseq (f : ℕ → ℕ) : list ℕ → bool
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
    simp[e, list.rnth_concat_length, h.1], refl },
  have lm0 : n0 = f l0.length,
  { have h' := h l0.length (lt_add_one (list.length l0)),
    simp [list.rnth_concat_length] at h',
    exact option.some_inj.mp h' },
  have lm1 : (l0 ⊂ₘ f) = tt,
  { apply ih.mpr, intros n ne,
    have h' := h n (nat.lt.step ne), rw ← h',
    simp[list.rnth], symmetry, exact list.nth_append (by simp[ne]) },
  exact ⟨lm0, lm1⟩
end

namespace rcomputable

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem nat_initial_code {f : ℕ → ℕ} : nat.initial_code f computable_in (f : ℕ →. ℕ) :=
let inif := (λ n, n.elim [] (λ y IH, f y :: IH) : ℕ → list ℕ) in
have c₀ : computable (λ x, [] : ℕ → list ℕ) := computable.const [],
have c₁ : (λ x, f x.2.1 :: x.2.2 : ℕ × ℕ × list ℕ → list ℕ) computable_in (f : ℕ →. ℕ) :=
  computable.list_cons.to_rcomp.comp
    (rcomputable.pair (rcomputable.refl.comp $ rcomputable.fst.comp rcomputable.snd)
      (rcomputable.snd.comp rcomputable.snd)),
((rcomputable.id.nat_elim c₀.to_rcomp c₁).of_eq $ λ n, 
by { simp, induction n with _ ih; simp, exact ih })

theorem initial_code [inhabited α] (f : α → β) :
  initial_code f computable_in (f : α →. β) :=
have l0 : (λ n, encode (f ((decode α n).get_or_else (default α)))) computable_in (f : α →. β) :=
  rpartrec.encode2_rpartrec_in (f : α →. β),
have l1 : initial_code f computable_in (λ n, encode (f ((decode α n).get_or_else (default α))) : ℕ →. ℕ) :=
  rcomputable.nat_initial_code,
l1.trans l0

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

theorem graph_rcomp (f : α → β) [∀ x y, decidable (@eq β x y)] : graph f computable_in (f : α →. β) :=
  have c₀ : (λ x, to_bool (x.1 = x.2) : β × β → bool) computable_in (f : α →. β) := primrec.eq.to_comp.to_rcomp,
  have c₂ : (λ x, (f x.1, x.2) : α × β → β × β) computable_in (f : α →. β) := rcomputable.pair 
  (rcomputable.refl.comp rcomputable.fst) rcomputable.snd,
c₀.comp c₂

theorem subseq_rcomputable (f : ℕ → ℕ) : list.subseq f computable_in (f : ℕ →. ℕ) :=
begin
  let g := (λ x, (x.2.1 + 1, x.2.2 && graph f (x.2.1, x.1)) : ℕ × ℕ × bool → ℕ × bool),
  let subseq0 := (λ x, (list.foldr (λ y z, g (y, z)) (0, tt) x) : list ℕ → ℕ × bool),
  let subseq1 := (λ x, (subseq0 x).2),
  have cg : g computable_in (f : ℕ →. ℕ) := ((computable.succ.to_rcomp).comp (fst.comp snd)).pair 
  (((primrec.dom_bool₂ band).to_comp.to_rcomp).comp $
    (snd.comp snd).pair $
      (rcomputable.graph_rcomp f).comp ((fst.comp snd).pair fst)),
  have cic : subseq1 computable_in (f : ℕ →. ℕ) := rcomputable.snd.comp ((rcomputable.foldr0 g (0, tt)).trans cg),
  have e : ∀ l, subseq0 l = (l.length, list.subseq f l),
  { intros l, simp[subseq0], induction l with ld ll ihl; simp[list.subseq,graph],
    rw ihl, simp, rw bool.band_comm, simp [eq_comm], congr },
  exact (cic.of_eq $ λ l, by simp[subseq1,e])
end

end rcomputable