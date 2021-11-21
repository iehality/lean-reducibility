import degree

variables 
  {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {o_dom : Type*} {o_cod : Type*}
  [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable o_dom] [primcodable o_cod]

def pfun.index_of (f : α →. β) (e : ℕ) : Prop := ⟦e⟧⁰ = f

def index_of (f : α → β) (e : ℕ) : Prop := ∀ a, f a ∈ (⟦e⟧⁰ a : part β)

structure complexity_measure (o : o_dom → o_cod) :=
(measure : ℕ → ℕ →. ℕ)
(convergence : ∀ e x, (⟦e⟧^o x : part ℕ).dom ↔ (measure e x).dom)
(effective : rcomputable_pred {n : ℕ × ℕ × ℕ | n.1 ∈ measure n.2.1 n.2.2} ↑ᵣo)

namespace complexity_measure

instance (o : o_dom → o_cod) : has_coe_to_fun (complexity_measure o) (λ _, ℕ → ℕ →. ℕ) := ⟨measure⟩

def time_complexity (o : o_dom → o_cod) : complexity_measure o :=
{ measure := use ℕ ↑ₒo,
  convergence := λ e x, (iff.symm use_dom_iff),
  effective := ⟨classical.dec_pred _, by { simp,
    have : (λ (a : ℕ × ℕ × ℕ), to_bool (usen ℕ ↑ₒo a.2.1 a.1 a.2.2 = option.some a.1)) computable_in! o,
    { refine (rcomputable.to_bool_eq (option ℕ) _ rcomputable.option_some.to_unary₁),
      refine rcomputable.usen_tot ℕ rcomputable.refl rcomputable.fst.to_unary₂ rcomputable.fst rcomputable.snd.to_unary₂ },
    exact this.of_eq (by { simp, intros u, simp, intros e x, exact iff.symm use_eq_iff }) }⟩ }

variables {o : o_dom → o_cod} (Φ : complexity_measure o)

def class_of (f : ℕ → ℕ) (g : ℕ → ℕ) : Prop := ∃ e, index_of g e ∧ ∀ a, Φ e a ≼ f a

def O_class_of (f : ℕ → ℕ) (g : ℕ → ℕ) : Prop := ∃ e, index_of g e ∧ ∃ a₀ n, ∀ a > a₀, Φ e a ≼ n * f a

def time_complexity.DTIME (o : o_dom → o_cod) (f : ℕ → ℕ) : (ℕ → ℕ) → Prop := O_class_of (time_complexity o) f

notation `DTIME^` o :max := time_complexity.DTIME o

def time_complexity.P (o : o_dom → o_cod) (f : ℕ → ℕ) : Prop := ∃ n : ℕ, DTIME^o (λ x, x^n) f

notation `P^` o :max := time_complexity.P o

end complexity_measure 
