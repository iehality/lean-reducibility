import degree

variables 
  {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {o_dom : Type*} {o_cod : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable o_dom] [primcodable o_cod]

structure complexity_measure (α : Type*) (β : Type*) [primcodable α] [primcodable β] :=
(measure : ℕ → α →. ℕ)
(convergence : ∀ e x, (⟦e⟧⁰ x : part β).dom ↔ (measure e x).dom)
(effective : computable_pred {n : ℕ × ℕ × α | n.1 ∈ measure n.2.1 n.2.2})

namespace complexity_measure 
variables (Φ : complexity_measure α β)

instance : has_coe_to_fun (complexity_measure α β) (λ _, ℕ → α →. ℕ) := ⟨measure⟩

def time_complexity : complexity_measure α β :=
{ measure := use0 β,
  convergence := λ e x, (iff.symm use_dom_iff),
  effective := ⟨classical.dec_pred _, by { simp,
    have : computable (λ (a : ℕ × ℕ × α), to_bool (usen0 β a.2.1 a.1 a.2.2 = option.some a.1)),
    { refine (rcomputable.to_bool_eq (option ℕ) _ rcomputable.option_some.to_unary₁).computable_of_rcomp,
      simp[usen0],
      refine rcomputable.usen_tot β (rcomputable.const 0) rcomputable.fst.to_unary₂ rcomputable.fst rcomputable.snd.to_unary₂ },
    exact this.of_eq (by { simp, intros u, simp, intros e x, exact iff.symm use_eq_iff }) }⟩ }

end complexity_measure 
