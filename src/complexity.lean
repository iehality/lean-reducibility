import degree

variables {o_dom : Type*} {o_cod : Type*} [primcodable o_dom] [primcodable o_cod]

structure admissible_numbering :=
(numbering : ℕ → ℕ →. ℕ)
(to_univ : ℕ → ℕ)
(to_univ_computable : computable to_univ)
(inv_univ : ℕ → ℕ)
(inv_univ_computable : computable inv_univ)
(numbering_to_univ : ∀ e, numbering e = ⟦to_univ e⟧⁰)
(numbering_inv_univ : ∀ e, numbering (inv_univ e) = ⟦e⟧⁰)

namespace admissible_numbering

instance : has_coe_to_fun admissible_numbering (λ _, ℕ → ℕ →. ℕ) := ⟨numbering⟩

def canonical : admissible_numbering :=
{ numbering := univ0 ℕ ℕ,
  to_univ := id,
  to_univ_computable := computable.id,
  inv_univ := id,
  inv_univ_computable := computable.id,
  numbering_to_univ := λ e, rfl,
  numbering_inv_univ := λ e, rfl }

variables {φ : admissible_numbering}
open rcomputable rcomputable₂

theorem exists_index {f : ℕ →. ℕ} :
  partrec f ↔ ∃ e, φ e = f :=
calc
  partrec f ↔ f partrec_in (λ _, some 0 : ℕ →. ℕ) : ⟨λ h, h.to_rpart, λ h, rpartrec.le_part_part h (computable.const _)⟩
        ... ↔ ∃ e, ⟦e⟧⁰ = f                       : rpartrec.exists_index
        ... ↔ ∃ e, φ e = f
  : ⟨by { rintros ⟨e, rfl⟩, refine ⟨φ.inv_univ e, φ.numbering_inv_univ _⟩ },
     by { rintros ⟨e, rfl⟩, refine ⟨φ.to_univ e, eq.symm (φ.numbering_to_univ _)⟩ }⟩

theorem recursion :
  ∃ fixpoint : ℕ → ℕ, computable fixpoint ∧
  ∀ {I : ℕ → ℕ} {i}, φ i = ↑ᵣI →
    φ (fixpoint i) = φ (I (fixpoint i)) :=
begin

end

theorem recursion {I : ℕ → ℕ} (h : computable I) :
  ∃ n, φ n = φ (I n) :=
begin

end

end admissible_numbering

structure complexity_measure (φ : admissible_numbering) :=
(measure : ℕ → ℕ →. ℕ)
(convergence : ∀ e n, (φ e n).dom ↔ (measure e n).dom)
(effective : computable_pred {n : ℕ × ℕ × ℕ | n.1 ∈ measure n.2.1 n.2.2})

namespace complexity_measure 
variables {φ : admissible_numbering} (Φ : complexity_measure φ)

instance : has_coe_to_fun (complexity_measure φ) (λ _, ℕ → ℕ →. ℕ) := ⟨measure⟩



end complexity_measure 
