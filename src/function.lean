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

def list.rnth {α} (l : list α) := l.reverse.nth 

theorem list.rnth_ext {α} {l₁ l₂ : list α} (h : ∀ n, l₁.rnth n = l₂.rnth n) : l₁ = l₂ :=
list.reverse_inj.mp (list.ext h)

lemma list.rnth_concat_length {α} (n : α) (l : list α) : (n :: l).rnth l.length = n :=
by { simp[list.rnth], 
     have : l.length = l.reverse.length, simp,
     simp only [this, list.nth_concat_length], refl }

lemma list.rnth_append {α} {l₀ l₁ : list α} {n : ℕ} (hn : n < l₀.length) :
  (l₁ ++ l₀).rnth n = l₀.rnth n :=
by { simp[list.rnth], exact list.nth_append (by simp; exact hn) }

@[simp] def initial_code {α} (f : ℕ → α) : ℕ → list α
| 0            := []
| (nat.succ n) := f n :: initial_code n

infix `↾`:70 := initial_code

@[simp] theorem nat.initial_code_length {α} (f : ℕ → α) (s) : (f↾s).length = s :=
by { induction s with m ih; simp, simp [ih] }

lemma nat.initial_code_nth0 {α} (f : ℕ → α) (s n) : (f↾(n + s + 1)).rnth n = f n :=
begin
  induction s with n0 ihn0,
  { simp[list.rnth],
    suffices a : ((f↾n).reverse ++ [f n]).nth (f↾ n).reverse.length = ↑(f n),
    { simp at a, exact a },
    { rw list.nth_concat_length, refl } },
  { simp[list.rnth] at ihn0,
    suffices a : ((f↾(n + n0)).reverse ++ [f (n + n0)] ++ [f (n + n0.succ)]).nth n = ↑(f n),
    { simp[list.rnth], simp at a, exact a },
  { rw list.nth_append, exact ihn0, simp, linarith }},
end

@[simp] theorem nat.initial_code_nth {s n} (h : n < s) {α} (f : ℕ → α): (f↾s).rnth n = f n :=
by { have e : s = n + (s - n - 1) + 1, omega, rw e, exact nat.initial_code_nth0 _ _ _ }

@[simp] theorem nat.initial_code_rnth_none {s n} (h : s ≤ n) {α} (f : ℕ → α)  : (f↾ s).rnth n = none :=
list.nth_len_le (by simp; from h)

theorem initial_code_some {α} {f : ℕ → α} {s n a} :
  (f↾ s).rnth n = some a → f n = a :=
by { have : n < s ∨ s ≤ n := lt_or_ge n s, cases this; simp[this], unfold_coes, simp }

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

def list.bmerge : list bool → list bool → list bool
| []        l         := l
| l         []        := l
| (a :: xs) (b :: ys) := (a || b) :: (xs.bmerge ys)

def nat.rpartrec.code.use (f c n) := nat.rfind_opt (λ s, nat.rpartrec.code.evaln s f c n)

namespace primrec

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem list_rnth : primrec₂ (@list.rnth α) := 
primrec.list_nth.comp (primrec.list_reverse.comp primrec.fst) primrec.snd

theorem list_bmerge : primrec₂ list.bmerge :=
by sorry

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

protected theorem epsilon_r [inhabited β] {p : α → β →. bool} {g : γ →. σ} :
  prod.unpaired p partrec_in g → (λ a, epsilon_r (p a)) partrec_in g :=
epsilon_r_rpartrec_refl.trans

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

theorem initial_code (f : ℕ → α) : (↾) f computable_in (f : ℕ →. α) :=
begin
  have c₀ := computable.const [],
  have c₁ := computable.list_cons.to_rcomp.comp
      (rcomputable.pair (rcomputable.refl.comp $ rcomputable.fst.comp rcomputable.snd)
        (rcomputable.snd.comp rcomputable.snd)),
  exact ((rcomputable.id.nat_elim c₀.to_rcomp c₁).of_eq $ λ n, 
  by { simp, induction n with _ ih; simp, exact ih })
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
  have c₀ : (λ x, to_bool (x.1 = x.2) : β × β → bool) computable_in (f : α →. β) := primrec.eq.to_comp.to_rcomp,
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
  (((primrec.dom_bool₂ band).to_comp.to_rcomp).comp $
    (snd.comp snd).pair $
      (rcomputable.graph_rcomp f).comp ((fst.comp snd).pair fst)),
  have cic : subseq1 computable_in (f : ℕ →. α) := rcomputable.snd.comp ((rcomputable.foldr0 g (0, tt)).trans cg),
  have e : ∀ l, subseq0 l = (l.length, list.subseq f l),
  { intros l, simp[subseq0], induction l with ld ll ihl; simp[list.subseq,graph],
    rw ihl, simp, rw bool.band_comm, simp [eq_comm], congr },
  exact (cic.of_eq $ λ l, by simp[subseq1,e])
end

end rcomputable

open nat.rpartrec primrec

-- !!!! AXIOM !!!! 
axiom computable.evaln_list :
  computable (λ x : ℕ × list ℕ × code × ℕ, code.evaln x.1 x.2.1.rnth x.2.2.1 x.2.2.2)

theorem rcomputable.evaln (f : ℕ → ℕ) : 
  (λ x : ℕ × code × ℕ, code.evaln x.1 (↑ₒf) x.2.1 x.2.2) computable_in ↑ᵣf :=
begin
  let u := (λ x : ℕ × code × ℕ,
    code.evaln x.1 (f↾x.1).rnth x.2.1 x.2.2),
  have eqn_u : u = (λ x : ℕ × code × ℕ, code.evaln x.1 (↑ₒf) x.2.1 x.2.2),
  { suffices :
      ∀ s c, code.evaln s (f↾s).rnth c = code.evaln s (↑ₒf) c,
    { funext, simp[u] at this ⊢, rw this },
    intros s c,
    apply code.evaln_use,
    intros u eqn_u,
    simp [nat.initial_code_nth eqn_u, coe_opt], 
    unfold_coes },
  rw ←eqn_u,
  simp[u],  
  let m := (λ x : ℕ × code × ℕ, (x.1, f↾x.1, x.2)),
  have := rcomputable.initial_code f,
  have : m computable_in ↑ᵣf := rcomputable.fst.pair 
    (((rcomputable.initial_code _).comp rcomputable.fst).pair rcomputable.snd),
  have := computable.evaln_list.to_rcomp.comp this,
  exact this,
end

theorem eval_eq_rfind (f : ℕ → option ℕ) (c n) :
  code.eval f c n = nat.rfind_opt (λ k, code.evaln k f c n) :=
roption.ext $ λ x, begin
  refine code.evaln_complete.trans (nat.rfind_opt_mono _).symm,
  intros a m n hl, apply code.evaln_mono hl,
end

theorem rpartrec.eval (f : ℕ → ℕ) :
  (λ n : code × ℕ, code.eval (↑ₒf) n.1 n.2) partrec_in ↑ᵣf :=
begin
  have := (rcomputable.evaln f).comp
    (snd.pair ((fst.comp fst).pair (snd.comp fst))).to_comp.to_rcomp,
  have := rpartrec.rfind_opt this,
  exact (this.of_eq $ λ n, by simp[eval_eq_rfind])
end 

variables {α : Type*} {σ : Type*} {β : Type*} {τ : Type*} {γ : Type*} {μ : Type*} 
variables [primcodable α] [primcodable σ] [primcodable β] [primcodable τ] [primcodable γ] [primcodable μ]

theorem rcomputable.univn (α σ) [primcodable α] [primcodable σ] (f : β → τ) :
  (λ x, ⟦x.2.1⟧^f [x.1] x.2.2 : ℕ × ℕ × α → option σ) computable_in ↑ᵣf :=
begin
  simp[univn],
  let f1 := (λ n, (decode β n).bind (λ b, some $ encode (f b))),
  have c₁ : (λ n, roption.of_option (f1 n)) partrec_in ↑ᵣf,
  { have e : (λ n, roption.of_option ((decode β n).bind (λ b, some $ encode (f b)))) =
      (λ n, roption.bind (decode β n) (λ b, some $ encode (f b))),
    { funext a, cases decode β a with v; simp[roption.of_option, coe_opt]},
    rw e,
    have := (rpartrec.refl_in (λ b, some $ encode (f b))).map
      (primrec.encode.comp snd).to_comp.to_rcomp, 
    have := (computable.of_option (computable.decode)).to_rpart.bind
      (this.comp rcomputable.snd),
    simp at this, exact this },
  have c₀ := (code.evaln_computable f1).comp 
    ((fst.pair ((primrec.of_nat code).comp $ fst.comp snd)).pair
    (primrec.encode.comp $ snd.comp snd)).to_comp.to_rcomp,
  have := rpartrec.trans c₀ c₁,
  have c₂ : (λ (a : ℕ × ℕ × α), code.evaln a.fst f1 (of_nat code a.snd.fst)
    (encode a.snd.snd)) computable_in (λ b, some $ encode (f b)) := this,
  have c₃ := primrec.decode.comp snd,
  have := c₂.option_bind c₃.to_comp.to_rcomp,
  exact this,
end

theorem rpartrec.univ (α σ) [primcodable α] [primcodable σ] (f : β → τ) :
  (λ x, ⟦x.1⟧^f x.2 : ℕ × α →. σ) partrec_in ↑ᵣf :=
begin
  simp[univ], unfold_coes,
  let f1 := (λ (n : ℕ), (decode β n).bind (λ b, some $ encode (f b))),
  have c₁ : (λ n, roption.of_option (f1 n)) partrec_in ↑ᵣf,
  { simp[f1],
    have e : (λ (n : ℕ), roption.of_option ((decode β n).bind (λ b, some $ encode (f b)))) =
      (λ (n : ℕ), roption.bind (decode β n) (λ b, roption.map encode (↑ₒf b))),
    { funext a, cases decode β a with v; simp[roption.of_option, coe_opt] },
    rw e,
    have := (rpartrec.refl_in (λ b, some $ encode (f b))).map
      (primrec.encode.comp snd).to_comp.to_rcomp, 
    have := ((computable.decode).of_option).to_rpart.bind
      (this.comp rcomputable.snd), simp at this,
    exact this },
  have c₀ := (code.eval_partrec f1).comp 
    (((primrec.of_nat code).comp fst).pair
    (primrec.encode.comp snd)).to_comp.to_rcomp,
  have c₂ := c₀.trans c₁,
  have c₃ := computable.decode.of_option ,
  have := c₂.bind (c₃.to_rpart.comp rcomputable.snd),
  exact this,
end

namespace rpartrec

protected theorem cond {c : α → bool} {f : α →. σ} {g : α →. σ} {h : β → τ}
  (hc : c computable_in ↑ᵣh) (hf : f partrec_in ↑ᵣh) (hg : g partrec_in ↑ᵣh) :
  (λ a, cond (c a) (f a) (g a)) partrec_in ↑ᵣh :=
let ⟨e, eqn_e⟩ := rpartrec.rpartrec_univ_iff_total.1 hf,
    ⟨i, eqn_i⟩ := rpartrec.rpartrec_univ_iff_total.1 hg in
begin
  have c₀ := ((rpartrec.univ α σ h).comp $
    (rcomputable.cond hc (rcomputable.const e) (rcomputable.const i)).pair rcomputable.id),
  simp at c₀,
  exact (c₀.of_eq $ λ x, by cases c x; simp[eqn_e, eqn_i] )
end

theorem bool_to_roption (c : α → bool):
  (λ a, cond (c a) (some 0) none : α →. ℕ) partrec_in (c : α →. bool) :=
rpartrec.cond rcomputable.refl (rcomputable.const 0) partrec.none.to_rpart

theorem universal_index {f : β → τ} : ∃ u, ∀ (x : ℕ) (y : α),
  (⟦u⟧^f (x, y) : roption σ) = ⟦x⟧^f y :=
by rcases rpartrec.rpartrec_univ_iff_total.mp (rpartrec.univ α σ f) with ⟨u, hu⟩;
   exact ⟨u, by simp[hu]⟩

theorem recursion (α σ) [primcodable α] [primcodable σ] (f : β → τ) :
  ∃ fixpoint : ℕ → ℕ, primrec fixpoint ∧
  (∀ {I : ℕ → ℕ} {i}, ⟦i⟧^f = ↑ᵣI →
    (⟦fixpoint i⟧^f : α →. σ) = ⟦I (fixpoint i)⟧^f) :=
begin
  have : ∃ j, ⟦j⟧^f = λ (a : ℕ × α), (⟦a.1⟧^f a.1).bind (λ (x : ℕ), ⟦x⟧^f a.2),
  { have this := ((rpartrec.univ ℕ ℕ f).comp (fst.pair fst).to_comp.to_rcomp).bind
      ((rpartrec.univ α σ f).comp (snd.pair (snd.comp primrec.fst)).to_comp.to_rcomp),
    exact rpartrec.rpartrec_univ_iff_total.mp this },
  rcases this with ⟨j, lmm_j⟩,
  have : ∃ k, ⟦k⟧^f = λ (a : ℕ × ℕ), ⟦a.1⟧^f (curry j a.2),
  { have := rpartrec.curry_prim.to_comp.comp (computable.const j) computable.id,
    have := (rpartrec.univ _ ℕ f).comp (rcomputable.fst.pair
      (this.to_rcomp.comp rcomputable.snd)),
    exact rpartrec.rpartrec_univ_iff_total.mp this },
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
   rcases rpartrec.rpartrec_univ_iff_total.mp h with ⟨i, hi⟩;
   exact ⟨fixpoint i, hfix hi⟩

end rpartrec

namespace partrec

theorem code.eval_list :
  partrec (λ x : list ℕ × code × ℕ, code.eval x.1.rnth x.2.1 x.2.2) :=
begin
  let f := (λ x : list ℕ × code × ℕ, nat.rfind_opt (λ s, code.evaln s x.1.rnth x.2.1 x.2.2)),
  have : partrec f := (partrec.rfind_opt $
    computable.evaln_list.comp (snd.pair fst).to_comp),
  exact (this.of_eq $ by simp[f, eval_eq_rfind])
end

theorem eval_list (α σ) [primcodable α] [primcodable σ]:
  partrec (λ x : ℕ × list β × α, (⟦x.1⟧*x.2.1.rnth x.2.2 : roption σ)) :=
begin
  simp [univ],
  have eqn : ∀ l : list β, (λ n, option.map encode (l.rnth n)) = (list.map encode l).rnth,
  { intros l, funext n, simp [list.rnth, ←list.map_reverse] },
  let f := (λ x : ℕ × list β × α, (list.map encode x.2.1, of_nat code x.1, encode x.2.2)),
  have pf : primrec f :=
    (primrec.list_map (primrec.fst.comp primrec.snd) (primrec.encode.comp primrec.snd).to₂).pair
    (((primrec.of_nat code).comp $ primrec.fst).pair
      (primrec.encode.comp $ primrec.snd.comp primrec.snd)),
  have := (code.eval_list.comp pf.to_comp).bind 
    (primrec.decode.comp primrec.snd).to_comp.of_option.to₂, 
  exact (this.of_eq $ by simp [eqn]),
end


end partrec