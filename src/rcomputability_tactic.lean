import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import rpartrec

section
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ] [primcodable τ] [primcodable μ]
  {o : σ →. τ}

#check option.get_or_else

theorem rcomputable.unpaired3 {f : β → γ → δ → σ} {g : α → β} {h : α → γ} {i : α → δ} {o : τ →. μ}
  (hf : (prod.unpaired3 f) computable_in o)
  (hg : g computable_in o) (hh : h computable_in o) (hi : i computable_in o) :
  (λ a : α, f (g a) (h a) (i a)) computable_in o :=
hf.comp (hg.pair (hh.pair hi))

lemma rcomputable.option_get_or_else {f : α → option β} {g : α → β} {o : σ →. τ}
  (hf : f computable_in o) (hg : g computable_in o) : (λ x, option.get_or_else (f x) (g x)) computable_in o :=
rcomputable₂.comp (computable.option_get_or_else computable.fst computable.snd).to_rcomp hf hg

lemma rcomputable.option_some : (option.some : α → option α) computable_in o :=
computable.option_some.to_rcomp

lemma rcomputable.option_is_some : (option.is_some : option α → bool) computable_in o :=
primrec.option_is_some.to_rcomp

lemma rcomputable.option_iget [inhabited α] : (option.iget : option α → α) computable_in o :=
primrec.option_iget.to_rcomp

lemma rcomputable₂.list_rnth : (@list.rnth α) computable₂_in o := 
(primrec.list_nth.comp (primrec.list_reverse.comp primrec.fst) primrec.snd).to_rcomp

lemma rcomputable.option_or_else :
  ((<|>) : option β → option β → option β) computable₂_in o :=
primrec.option_orelse.to_rcomp

lemma rcomputable₂.to_bool_eq (α : Type*) [primcodable α] [decidable_eq α] :
  (λ x y : α, to_bool (x = y)) computable₂_in o := primrec.eq.to_rcomp

lemma rcomputable₂.to_bool_nat_lt : (λ m n : ℕ, to_bool (m < n)) computable₂_in o := primrec.nat_lt.to_rcomp

lemma rcomputable₂.to_bool_nat_le : (λ m n : ℕ, to_bool (m ≤ n)) computable₂_in o := primrec.nat_le.to_rcomp

lemma rcomputable.succ : nat.succ computable_in o := primrec.succ.to_rcomp

lemma rcomputable.pred : nat.pred computable_in o := primrec.pred.to_rcomp

lemma rcomputable₂.nat_add : ((+) : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_add.to_rcomp

lemma rcomputable₂.nat_sub : (has_sub.sub : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_sub.to_rcomp

lemma rcomputable₂.nat_mul : ((*) : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_mul.to_rcomp

lemma rcomputable₂.nat_min : (min : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_min.to_rcomp

lemma rcomputable₂.nat_max : (max : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_max.to_rcomp

lemma rcomputable.nat_bodd : nat.bodd computable_in o := primrec.nat_bodd.to_rcomp

lemma rcomputable.dom_fintype [fintype α] (f : α → β) : f computable_in o := (primrec.dom_fintype f).to_rcomp

lemma rcomputable.bnot : bnot computable_in o := primrec.bnot.to_rcomp

lemma rcomputable.band : band computable₂_in o := primrec.band.to_rcomp

lemma rcomputable.bor : bor computable₂_in o := primrec.bor.to_rcomp

@[protected]
lemma rcomputable.ite {c : α → Prop} [decidable_pred c] {f g : α → β}
  (hc : (λ x, to_bool (c x)) computable_in o) (hf : f computable_in o) (hg : g computable_in o):
  (λ a, if c a then f a else g a) computable_in o :=
(rcomputable.cond hc hf hg).of_eq (λ x, by by_cases C : c x; simp[C])


lemma rcomputable₂.list_cons : (list.cons : α → list α → list α) computable₂_in o := primrec.list_cons.to_rcomp

lemma rcomputable₂.list_nth : (list.nth : list α → ℕ → option α) computable₂_in o := primrec.list_nth.to_rcomp

lemma rcomputable₂.list_append : ((++) : list α → list α → list α) computable₂_in o := primrec.list_append.to_rcomp

lemma rcomputable.list_length : (list.length : list α → ℕ) computable_in o := primrec.list_length.to_rcomp

#check @list.rec

protected lemma rcomputable.of_nat (α : Type*) [denumerable α] : (denumerable.of_nat α) computable_in o :=
(primrec.of_nat α).to_rcomp

lemma rcomputable.option_get {f : α → option β} {h : ∀ a, (f a).is_some}
  (hf : f computable_in o) : (λ a, option.get (h a)) computable_in o :=
((rpartrec.nat_iff1.mp rcomputable.pred).comp hf).of_eq (λ n,
  by { simp,
       generalize hx : encodable.decode α n = x,
       cases x; simp,
       rcases C : f x,
       { exfalso, have := h x, simp[C] at this, contradiction },
       { simp[C] } })

lemma rcomputable.list_range_r : list.range_r computable_in o :=
begin
  have : (nat.elim [] (λ m IH, m :: IH)) computable_in o,
  { refine rcomputable.nat_elim' rcomputable.id (rcomputable.const [])
    (rcomputable₂.list_cons.comp rcomputable.fst.to_unary₂ rcomputable.snd.to_unary₂) },
  exact this.of_eq (λ n, by { induction n with n IH; simp[list.range_r], exact IH })
end

theorem rcomputable.option_rec {f : α → option β} {g : α → γ} {h : α → β → γ}
  (hf : f computable_in o) (hg : g computable_in o) (hh : h computable₂_in o) :
  @rcomputable _ _ γ _ _ _ _ _ (λ a, option.rec (g a) (h a) (f a)) o :=
rcomputable.option_cases hf hg hh

lemma rcomputable.computable_of_rcomp {f : α → β} (hf : f computable_in (λ n, none : ℕ →. ℕ)) : 
  computable f := rpartrec.le_part_part hf partrec.none

lemma rpartrec.partrec_of_rpart {f : α →. β} (hf : f partrec_in (λ n, none : ℕ →. ℕ)) : 
  partrec f := rpartrec.le_part_part hf partrec.none
#check nat.elim


end

@[user_attribute]
meta def rcomputability : user_attribute :=
{ name := `rcomputability,
  descr := "lemmas usable to prove relative computability" }

attribute [rcomputability]
  rcomputable.id
  rcomputable.id'
  rcomputable.fst
  rcomputable.snd
  rcomputable.pair
  rcomputable.const
  rcomputable.encode
  rcomputable.decode
  rcomputable.refl
  rcomputable.cond
  rcomputable.ite
  rcomputable.succ
  rcomputable.pred
  rcomputable.of_nat
  rcomputable.nat_cases
  rcomputable.option_cases
  rcomputable.option_rec
  rcomputable.option_bind
  rcomputable.option_map
  rcomputable.option_some
  rcomputable.option_is_some
  rcomputable.option_get_or_else
  rcomputable.option_or_else
  rcomputable.option_get
  rcomputable.option_iget
  rcomputable.nat_bodd
  rcomputable.dom_fintype
  rcomputable₂.list_cons
  rcomputable₂.list_nth
  rcomputable₂.list_append
  rcomputable.list_length
  rcomputable.list_range_r
  rcomputable₂.to_bool_eq
  rcomputable₂.to_bool_nat_lt
  rcomputable₂.to_bool_nat_le
  rcomputable₂.pair
  rcomputable₂.list_rnth
  rcomputable₂.nat_add
  rcomputable₂.nat_sub
  rcomputable₂.nat_mul
  rcomputable₂.nat_min
  rcomputable₂.nat_max
  rcomputable.bnot
  rcomputable.band
  rcomputable.bor

  rpartrec.refl
  rpartrec.of_option
  rpartrec.of_option'
  rpartrec.coe
  rpartrec.some
  rpartrec.bind
  rpartrec.map
  rpartrec.rfind
  rpartrec.rfind_opt

open tactic.interactive («have»)
open tactic (get_local infer_type)

namespace tactic
namespace interactive

setup_tactic_parser

meta def goal_is_partrec : tactic unit := do t ← tactic.target,
  match t with
  | `(partrec %%r) := skip
  | _              := failed
  end

meta def goal_is_computable : tactic unit := do t ← tactic.target,
  match t with
  | `(computable %%r) := skip
  | _                 := failed
  end

meta def goal_is_rpartrec : tactic unit := do t ← tactic.target,
  match t with
  | `(rpartrec %%l %%r)     := skip
  | `(rpartrec_tot %%l %%r) := skip
  | _ := failed
  end

meta def goal_is_rcomputable : tactic unit := do t ← tactic.target,
  match t with
  | `(rcomputable %%l %%r)     := skip
  | `(rcomputable_tot %%l %%r) := skip
  | _ := failed
  end

meta def goal_is_rpartrec₂ : tactic unit := do t ← tactic.target,
  match t with
  | `(rpartrec₂ %%l %%r)     := skip
  | `(rpartrec₂_tot %%l %%r) := skip
  | _ := failed
  end

meta def goal_is_rcomputable₂ : tactic unit := do t ← tactic.target,
  match t with
  | `(rcomputable₂ %%l %%r)     := skip
  | `(rcomputable₂_tot %%l %%r) := skip
  | _ := failed
  end

meta def rcomputability_tactics (md : transparency := semireducible) : list (tactic string) :=
[ propositional_goal >> apply_assumption >> pure "apply_assumption",
  goal_is_partrec >> `[refine rpartrec.partrec_of_rpart _] >> pure "refine rpartrec.partrec_of_rpart _",
  goal_is_computable >> `[refine rcomputable.computable_of_rcomp _] >> pure "refine rcomputable.computable_of_rcomp _",
  apply_rules [``(rcomputability)] 50 { md := md } >> pure "apply_rules rcomputability",
  `[refine rcomputable.to_unary₁ _]  >> pure "refine rcomputable.to_unary₁ _",
  `[refine rcomputable.to_unary₂ _]  >> pure "refine rcomputable.to_unary₂ _",
  `[refine rpartrec.to_unary₁ _]     >> pure "refine rpartrec.to_unary₁ _",
  `[refine rpartrec.to_unary₂ _]     >> pure "refine rpartrec.to_unary₂ _",
  goal_is_rcomputable₂ >> `[refine rcomputable₂.comp₂ _ _ _; try { exact rpartrec.some };
    fail_if_success { exact rcomputable.id }] >> pure "refine rcomputable₂.comp₂ _ _ _",
  goal_is_rcomputable  >> `[refine rcomputable₂.comp _ _ _; try { exact rpartrec.some };  
    fail_if_success { exact rcomputable.id }] >> pure "refine rcomputable₂.comp _ _ _",  
  goal_is_rpartrec₂    >> `[refine rpartrec₂.comp₂ _ _ _; try { exact rpartrec.some };    
    fail_if_success { exact rcomputable.id }] >> pure "refine rpartrec₂.comp₂ _ _ _",
  goal_is_rpartrec     >> `[refine rpartrec₂.comp _ _ _; try { exact rpartrec.some };     
    fail_if_success { exact rcomputable.id }] >> pure "refine rpartrec₂.comp _ _ _",
  goal_is_rcomputable₂ >> `[refine rcomputable.comp₂ _ _; try { exact rpartrec.some };    
    fail_if_success { exact rcomputable.id }] >> pure "refine rcomputable.comp₂ _ _",  
  goal_is_rcomputable  >> `[refine rcomputable.comp _ _; try { exact rpartrec.some };     
    fail_if_success { exact rcomputable.id }] >> pure "refine rcomputable.comp _ _",  
  goal_is_rpartrec     >> `[refine rpartrec.comp _ _; try { exact rpartrec.some };        
    fail_if_success { exact rcomputable.id }] >> pure "refine rpartrec.comp _ _",
  goal_is_rpartrec₂    >> `[refine rpartrec.comp₂ _ _; try { exact rpartrec.some };       
    fail_if_success { exact rcomputable.id }] >> pure "refine rpartrec.comp₂ _ _" ]

meta def rcomputability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md                  := if bang.is_some then semireducible else reducible,
    rcomputability_core := tactic.tidy { tactics := rcomputability_tactics md, ..cfg },
    trace_fn            := if trace.is_some then show_term else id in
trace_fn rcomputability_core
end interactive

end tactic

open encodable

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] {o : σ →. τ}

example (f : ℕ →. ℕ) (p : ℕ → ℕ →. bool) (h : p partrec₂_in f) :
  (λ x : ℕ, (nat.rfind (p x)).map (λ y, (y, (y, 0, x)))) partrec_in f :=
by { rcomputability }

example {f : α → ℕ → option σ} {g : β →. τ}(hf : f computable₂_in g) :
  (λ (a : α), ↑(λ (n : ℕ), (f a n).is_some) : α → ℕ →. bool) partrec₂_in g :=
by { unfold_coes, simp[pfun.lift],
     rcomputability }


#check @rcomputable.id