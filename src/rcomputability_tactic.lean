import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import rpartrec

namespace rcomputable
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

#check option.get_or_else

lemma option_get_or_else {f : α → option β} {g : α → β} {o : σ →. τ}
  (hf : f computable_in o) (hg : g computable_in o) : (λ x, option.get_or_else (f x) (g x)) computable_in o :=
rcomputable₂.comp (computable.option_get_or_else computable.fst computable.snd).to_rcomp hf hg


end rcomputable

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
  rcomputable.nat_cases'
  rcomputable.option_cases'
  rcomputable.option_bind'
  rcomputable.option_map'
  rcomputable.option_get_or_else
  rcomputable₂.pair
  rpartrec.refl
  rpartrec.of_option
  rpartrec.of_option_refl
  rpartrec.bind'
  rpartrec.map'
  rpartrec.rfind'
  rpartrec.rfind_opt'

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
  goal_is_rcomputable₂ >> `[refine rcomputable₂.comp₂ _ _ _; fail_if_success { exact rcomputable.id }] >> pure "refine rcomputable₂.comp₂ _ _ _",
  goal_is_rcomputable  >> `[refine rcomputable₂.comp _ _ _; fail_if_success { exact rcomputable.id }]  >> pure "refine rcomputable₂.comp _ _ _",  
  goal_is_rpartrec₂    >> `[refine rpartrec₂.comp₂ _ _ _; fail_if_success { exact rcomputable.id }]    >> pure "refine rpartrec₂.comp₂ _ _ _",
  goal_is_rpartrec     >> `[refine rpartrec₂.comp _ _ _; fail_if_success { exact rcomputable.id }]     >> pure "refine rpartrec₂.comp _ _ _",
  goal_is_rcomputable₂ >> `[refine rcomputable.comp₂ _ _ _; fail_if_success { exact rcomputable.id }]  >> pure "refine rcomputable.comp₂ _ _ _",  
  goal_is_rcomputable  >> `[refine rcomputable.comp _ _ _; fail_if_success { exact rcomputable.id }]   >> pure "refine rcomputable.comp _ _ _",  
  goal_is_rpartrec     >> `[refine rpartrec.comp _ _ _; fail_if_success { exact rcomputable.id }]      >> pure "refine rpartrec.comp _ _ _" ]

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

variables {β : Type*} [primcodable β] [inhabited β] {α : Type*} [primcodable α]

example (f : ℕ →. ℕ) (p : ℕ → ℕ →. bool) (h : p partrec₂_in f) :
  (λ x : ℕ, (nat.rfind (p x)).map (λ y, (y, (y, 0, x)))) partrec_in f :=
by { exact (rpartrec.rfind' h).map'
  (rcomputable.id'.to_unary₂.pair
     (rcomputable.id'.to_unary₂.pair ((rcomputable.const 0).to_unary₁.pair rcomputable.id'.to_unary₁)))}

