import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import rpartrec

namespace rcomputable
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

end rcomputable

@[user_attribute]
meta def rcomputability : user_attribute :=
{ name := `rcomputability,
  descr := "lemmas usable to prove relative computability" }

attribute [rcomputability]
  rcomputable.id
  rcomputable.fst
  rcomputable.snd
  rcomputable.nat_elim
  rcomputable.pair
  rcomputable.const
  rcomputable.encode
  rcomputable.decode
  rcomputable.refl
  rcomputable.trans
  rcomputable.cond
  rcomputable.option_cases'
  rcomputable.option_bind'
  rcomputable.option_map'
  rpartrec.refl
  rpartrec.of_option
  rpartrec.of_option_refl
  rpartrec.nat_elim
  rpartrec.bind'
  rpartrec.map'
  rpartrec.rfind'
  rpartrec.rfind'_refl
  rpartrec.rfind_opt'
  rpartrec.nat_cases_right  

open tactic.interactive («have»)
open tactic (get_local infer_type)



namespace tactic
namespace interactive

setup_tactic_parser

meta def apply_rcomputable.comp : tactic unit :=
`[fail_if_success { exact rcomputable.const };
  refine rcomputable.comp _ _;
  fail_if_success { exact rcomputable.id }]

meta def apply_rcomputable.comp₂ : tactic unit :=
`[fail_if_success { exact rcomputable.const };
  refine rcomputable.comp₂ _ _;
  fail_if_success { exact rcomputable.id }]

meta def apply_rpcomputable.comp : tactic unit :=
`[refine rpartrec.comp _ _]

meta def apply_rpcomputable.comp₂ : tactic unit :=
`[refine rpartrec.comp₂ _ _]

meta def rcomputability_tactics (md : transparency := semireducible) : list (tactic string) :=
[ propositional_goal >> apply_assumption >> pure "apply_assumption",
  apply_rules [``(rcomputability)] 50 { md := md } >> pure "apply_rules rcomputability",
  apply_rcomputable.comp >> pure "refine rcomputable.comp _ _",
  apply_rcomputable.comp₂ >> pure "refine rcomputable.comp _ _",
  apply_rpcomputable.comp >> pure "refine rpartrec.comp _ _",
  apply_rpcomputable.comp₂ >> pure "refine rpartrec.comp _ _" ]

meta def rcomputability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md                  := if bang.is_some then semireducible else reducible,
    rcomputability_core := tactic.tidy { tactics := rcomputability_tactics md, ..cfg },
    trace_fn            := if trace.is_some then show_term else id in
trace_fn rcomputability_core
end interactive

end tactic



example (f : ℕ →. ℕ) (p : ℕ → ℕ →. bool) (h : prod.unpaired p partrec_in f) :
  (λ x : ℕ, (f x).bind (λ y, part.some (y, (y, 0, x)))) partrec_in f :=
by rcomputability! 

