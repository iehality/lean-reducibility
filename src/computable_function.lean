
import function coding

open encodable denumerable roption

def nat.rpartrec.code.use (f c n) := nat.rfind_opt (λ s, nat.rpartrec.code.evaln s f c n)

namespace primrec

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem list_rnth : primrec₂ (@list.rnth α) := 
primrec.list_nth.comp (primrec.list_reverse.comp primrec.fst) primrec.snd

theorem list_bmerge : primrec₂ list.bmerge :=
by sorry

end primrec

namespace partrec

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]
open nat.rpartrec
#check code.oracle_of_eq 


theorem code.eval_list_partrec :
  partrec (λ x : (code × list ℕ) × ℕ, code.eval x.1.2.rnth x.1.1 x.2) :=
begin
  have := primrec.list_nth.comp (primrec.list_reverse.comp $
    (primrec.of_nat (list ℕ)).comp $ primrec.fst.comp primrec.unpair)
    (primrec.snd.comp primrec.unpair),
  have := this.to_comp.of_option, simp at this,
  let N : ℕ → option ℕ := (λ x, option.none),
  have := this.to_rpart_in (λ x, N x),
  have := rpartrec.nat_iff.mp this,
  rcases code.exists_code_opt.mp this with ⟨c, hc⟩,
  let i := code.curry c, 
  let T := (λ x c, (i x).oracle_of c),
  have E : ∀ (l : list ℕ) d, code.eval N (T (encode l) d) = code.eval l.rnth d,
  { intros l e, simp[T],
    have : code.eval N (i (encode l)) = (λ x, l.rnth x),
    { funext n, simp[i, hc], refl },
    simp[code.oracle_of_eq this] },
  have ip : primrec i := code.curry_prim.comp (primrec.const c) (primrec.id), 
  have Tp : primrec₂ T := code.oracle_of_prim.comp (ip.comp $ primrec.fst)
    (primrec.snd), 
  suffices :
    (λ x : (code × list ℕ) × ℕ, code.eval x.1.2.rnth x.1.1 x.2) partrec_in (λ x, N x),
  from le_part_part this partrec.none,
  { simp [←E],
    have := primrec.pair (Tp.comp (primrec.encode.comp $ primrec.snd.comp primrec.fst) 
      (primrec.fst.comp primrec.fst)) primrec.snd,
    exact (code.eval_partrec N).comp this.to_comp.to_rcomp }
end

theorem code.evaln_list_partrec :
  computable (λ x : ℕ × list ℕ × code × ℕ, code.evaln x.1 x.2.1.rnth x.2.2.1 x.2.2.2) :=
begin
  have := primrec.list_nth.comp (primrec.list_reverse.comp $
    (primrec.of_nat (list ℕ)).comp $ primrec.fst.comp primrec.unpair)
    (primrec.snd.comp primrec.unpair),
  have := this.to_comp.of_option, simp at this,
  let N : ℕ → option ℕ := (λ x, option.none),
  have := this.to_rpart_in (λ x, N x),
  have := rpartrec.nat_iff.mp this,
  rcases code.exists_code_opt.mp this with ⟨c, hc⟩,
  let i := code.curry c, 
  let T := (λ x c, (i x).oracle_of c),
  let o := (λ x, [8].rnth x),
  have E : ∀ (l : list ℕ) d s, code.evaln s N (T (encode l) d) = code.evaln s o d,
  { intros l e, simp[T],
    apply code.evaln_oracle_of, intros s,
    funext n, simp [i, hc],

    },
  have ip : primrec i := code.curry_prim.comp (primrec.const c) (primrec.id), 
  have Tp : primrec₂ T := code.oracle_of_prim.comp (ip.comp $ primrec.fst)
    (primrec.snd), 
  suffices :
    (λ x : (code × list ℕ) × ℕ, code.eval x.1.2.rnth x.1.1 x.2) partrec_in (λ x, N x),
  from le_part_part this partrec.none,
  { simp [←E],
    have := primrec.pair (Tp.comp (primrec.encode.comp $ primrec.snd.comp primrec.fst) 
      (primrec.fst.comp primrec.fst)) primrec.snd,
    exact (code.eval_partrec N).comp this.to_comp.to_rcomp }
end

theorem eval_list_partrec (α σ) [primcodable α] [primcodable σ]:
  partrec (λ x : ℕ × list β × α, (⟦x.1⟧^x.2.1.rnth x.2.2 : roption σ)) :=
begin
  simp [univ],
  have el : ∀ l : list β, (λ n, option.map encode (l.rnth n)) = (list.map encode l).rnth,
  { intros l, funext n, simp [list.rnth, ←list.map_reverse] },
  let f := (λ x : ℕ × list β × α, ((of_nat code x.1, list.map encode x.2.1), encode x.2.2)),
  have pf : primrec f := (((primrec.of_nat code).comp $ primrec.fst).pair 
    (primrec.list_map (primrec.fst.comp primrec.snd) (primrec.encode.comp primrec.snd).to₂)).pair
    (primrec.encode.comp $ primrec.snd.comp primrec.snd),
  have := (code.eval_list_partrec.comp pf.to_comp).bind 
    (primrec.decode.comp primrec.snd).to_comp.of_option.to₂,
  exact (this.of_eq $ by simp [el]),
end

theorem eval_list_partrec' (α σ) [primcodable α] [primcodable σ]:
  partrec (λ x : (ℕ × list β) × α, (⟦x.1.1⟧^x.1.2.rnth x.2 : roption σ)) :=
begin
  simp [univ],
  have el : ∀ l : list β, (λ n, option.map encode (l.rnth n)) = (list.map encode l).rnth,
  { intros l, funext n, simp [list.rnth, ←list.map_reverse] },
  let f := (λ x : (ℕ × list β) × α, ((of_nat code x.1.1, list.map encode x.1.2), encode x.2)),
  have pf : primrec f := (((primrec.of_nat code).comp $ primrec.fst.comp primrec.fst).pair 
    (primrec.list_map (primrec.snd.comp primrec.fst) (primrec.encode.comp primrec.snd).to₂)).pair
    (primrec.encode.comp primrec.snd),
  have := (code.eval_list_partrec.comp pf.to_comp).bind 
    (primrec.decode.comp primrec.snd).to_comp.of_option.to₂,
  exact (this.of_eq $ by simp [el]),
end

end partrec

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

theorem eval_list_partrec {f : α → ℕ} {g : α → list bool} {h : α → β}
  (hf : computable f) (hg : computable g) (hh : computable h) :
  partrec (λ a, (⟦f a⟧^(g a).rnth (h a) : roption σ)) :=
by sorry

end rpartrec

namespace rcomputable

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

protected theorem epsilon [inhabited β] {p : α → β → bool} {g : γ →. σ}  :
  prod.unpaired p computable_in g → (λ a, epsilon (p a)) partrec_in g := λ cp,
rpartrec.epsilon_r cp

theorem initial_code {f : ℕ → α} : (↾) f computable_in (f : ℕ →. α) :=
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