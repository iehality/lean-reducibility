import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import rpartrec

section
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]
  {o : σ →. τ}

#check option.get_or_else

lemma rcomputable.option_get_or_else {f : α → option β} {g : α → β} {o : σ →. τ}
  (hf : f computable_in o) (hg : g computable_in o) : (λ x, option.get_or_else (f x) (g x)) computable_in o :=
rcomputable₂.comp (computable.option_get_or_else computable.fst computable.snd).to_rcomp hf hg

lemma rcomputable.option_some : (option.some : α → option α) computable_in o :=
computable.option_some.to_rcomp

lemma rcomputable.option_is_some : (option.is_some : option α → bool) computable_in o :=
primrec.option_is_some.to_rcomp

lemma rcomputable₂.list_rnth : (@list.rnth α) computable₂_in o := 
(primrec.list_nth.comp (primrec.list_reverse.comp primrec.fst) primrec.snd).to_rcomp

lemma rcomputable.option_or_else :
  ((<|>) : option β → option β → option β) computable₂_in o :=
primrec.option_orelse.to_rcomp

lemma rcomputable₂.to_bool_eq [decidable_eq α] : (λ x y : α, to_bool (x = y)) computable₂_in o := primrec.eq.to_rcomp

lemma rcomputable₂.to_bool_nat_lt : (λ m n : ℕ, to_bool (m < n)) computable₂_in o := primrec.nat_lt.to_rcomp

lemma rcomputable₂.to_bool_nat_le : (λ m n : ℕ, to_bool (m ≤ n)) computable₂_in o := primrec.nat_le.to_rcomp

lemma rcomputable₂.nat_add : ((+) : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_add.to_rcomp

lemma rcomputable₂.nat_sub : (has_sub.sub : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_sub.to_rcomp

lemma rcomputable₂.nat_mul : ((*) : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_mul.to_rcomp

lemma rcomputable₂.nat_min : (min : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_min.to_rcomp

lemma rcomputable₂.nat_max : (max : ℕ → ℕ → ℕ) computable₂_in o := primrec.nat_max.to_rcomp

lemma rcomputable.nat_bodd : nat.bodd computable_in o := primrec.nat_bodd.to_rcomp

lemma rcomputable.dom_fintype [fintype α] (f : α → σ) : f computable_in o := (primrec.dom_fintype f).to_rcomp

lemma rcomputable.ite {c : α → Prop} [decidable_pred c] {f g : α → σ}
  (hc : (λ x, to_bool (c x)) computable_in o) (hf : f computable_in o) (hg : g computable_in o):
  (λ a, if c a then f a else g a) computable_in o :=
(rcomputable.cond hc hf hg).of_eq (λ x, by by_cases C : c x; simp[C])

lemma rcomputable₂.list_cons : (list.cons : α → list α → list α) computable₂_in o := primrec.list_cons.to_rcomp

lemma rcomputable₂.list_nth : (list.nth : list α → ℕ → option α) computable₂_in o := primrec.list_nth.to_rcomp

lemma rcomputable₂.list_append : ((++) : list α → list α → list α) computable₂_in o := primrec.list_append.to_rcomp

lemma rcomputable₂.list_length : (list.length : list α → ℕ) computable_in o := primrec.list_length.to_rcomp






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
  rcomputable.nat_cases
  rcomputable.option_cases
  rcomputable.option_bind
  rcomputable.option_map
  rcomputable.option_some
  rcomputable.option_is_some
  rcomputable.option_get_or_else
  rcomputable.option_or_else
  rcomputable.nat_bodd
  rcomputable.dom_fintype

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
  [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ]

example (f : ℕ →. ℕ) (p : ℕ → ℕ →. bool) (h : p partrec₂_in f) :
  (λ x : ℕ, (nat.rfind (p x)).map (λ y, (y, (y, 0, x)))) partrec_in f :=
by { rcomputability }

example {f : α → ℕ → option σ} {g : β →. τ}(hf : f computable₂_in g) :
  (λ (a : α), ↑(λ (n : ℕ), (f a n).is_some) : α → ℕ →. bool) partrec₂_in g :=
by { unfold_coes, simp[pfun.lift],
     rcomputability }

#check @rcomputable.id