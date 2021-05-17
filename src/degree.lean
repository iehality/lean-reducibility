import reducibility Kleene_Post
open encodable denumerable roption

local attribute [instance, priority 0] classical.prop_decidable

@[refl] theorem t_reducible_equiv.refl {α} [primcodable α] (A : set α) [D : decidable_pred A] :
  A ≡ₜ A :=
⟨t_reducible.refl A, t_reducible.refl A⟩

@[symm] theorem t_reducible_equiv.symm {α β} [primcodable α] [primcodable β]
  {A : set α} {B : set β} :
  A ≡ₜ B → B ≡ₜ A :=
and.swap

@[trans] theorem t_reducible_equiv.trans {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {A : set α} {B : set β} {C : set γ} :
  A ≡ₜ B → B ≡ₜ C → A ≡ₜ C :=
λ ⟨ab, ba⟩ ⟨bc, cb⟩, ⟨t_reducible.trans ab bc, t_reducible.trans cb ba⟩

theorem equivalence_of_t_reducible_equiv (α) [primcodable α] :
  equivalence (@t_reducible_equiv α α _ _) :=
⟨λ x, t_reducible_equiv.refl x, λ x y, t_reducible_equiv.symm, λ x y z, t_reducible_equiv.trans⟩

def turing_degree : Type :=
quotient (⟨t_reducible_equiv, equivalence_of_t_reducible_equiv ℕ⟩ : setoid (set ℕ))

notation `𝓓` := turing_degree

namespace turing_degree

def deg (A : set ℕ) : 𝓓 := quotient.mk' A

@[elab_as_eliminator]
protected lemma ind_on {C : 𝓓 → Prop} (d : 𝓓)
  (h : ∀ p : set ℕ, C (deg p)) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : 𝓓) (f : set ℕ → φ)
  (h : ∀ p q, p ≡ₜ q → f p = f q) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (p : set ℕ) (f : set ℕ → φ)
  (h : ∀ p q, t_reducible_equiv p q → f p = f q) : (deg p).lift_on f h = f p :=
rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : 𝓓) (f : set ℕ → set ℕ → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ≡ₜ q₁ → p₂ ≡ₜ q₂ → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (p q : set ℕ) (f : set ℕ → set ℕ → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ≡ₜ q₁ → p₂ ≡ₜ q₂ → f p₁ p₂ = f q₁ q₂) :
  (deg p).lift_on₂ (deg q) f h = f p q := rfl

@[simp] lemma of_eq_of {p q} : deg p = deg q ↔ p ≡ₜ q :=
by simp [deg, quotient.eq']

instance : has_le 𝓓 :=
⟨λ d₁ d₂, turing_degree.lift_on₂ d₁ d₂ (≤ₜ) $
  λ p₁ p₂ q₁ q₂ hp hq, propext ⟨λ hpq, (hp.2.trans hpq).trans hq.1, λ hpq, (hp.1.trans hpq).trans hq.2⟩⟩

instance : has_lt 𝓓 := ⟨λ d₀ d₁, d₀ ≤ d₁ ∧ ¬ d₁ ≤ d₀⟩

instance : has_zero 𝓓 := ⟨deg (∅ : set ℕ)⟩



instance : inhabited 𝓓 := ⟨0⟩

def djump : 𝓓 → 𝓓 :=
λ d, turing_degree.lift_on d (λ d, deg d′)
(λ A B ⟨ab, ba⟩, by { simp, exact ⟨le_le_jump ab, le_le_jump ba⟩ })

notation d`⁺`:1200 := djump d

def djump_itr (d : 𝓓) : ℕ → 𝓓
| 0 := d
| (n+1) := (djump_itr n)⁺

@[simp] lemma of_le_of {p q} : deg p ≤ deg q ↔ p ≤ₜ q := by refl

@[simp] lemma of_lt_of {p q} : deg p < deg q ↔ p <ₜ q := by refl

@[simp] lemma of_jump {A} : (deg A)⁺ = deg A′ := by refl

@[simp] theorem zero_minimum (d : 𝓓) : 0 ≤ d :=
by { induction d using turing_degree.ind_on, simp [has_zero.zero],
     exact computable_le d computable_0 }

def RE_degree := {d | ∃ R : set ℕ, re_pred R ∧ d = deg R}

notation `𝓡` := RE_degree

def High := {d | d ∈ 𝓡 ∧ d⁺ = 0⁺⁺}

def Low  := {d | d ∈ 𝓡 ∧ d⁺ = 0⁺}

private lemma le_refl (d : 𝓓) : d ≤ d :=
by induction d using turing_degree.ind_on; simp

private lemma le_antisymm {d₁ d₂ : 𝓓} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ :=
begin
  induction d₁ using turing_degree.ind_on,
  induction d₂ using turing_degree.ind_on,
  intros hp hq,
  simp only [*, t_reducible_equiv, of_le_of, of_eq_of, true_and] at *
end

private lemma le_trans {d₁ d₂ d₃ : 𝓓} :
  d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ :=
begin
  induction d₁ using turing_degree.ind_on,
  induction d₂ using turing_degree.ind_on,
  induction d₃ using turing_degree.ind_on,
  exact t_reducible.trans
end

instance : partial_order 𝓓 :=
{ le := (≤),
  le_refl := le_refl,
  le_trans := λ _ _ _, le_trans,
  le_antisymm := λ _ _, le_antisymm }

theorem lt_djump (d : 𝓓) : d < d⁺ :=
by { induction d using turing_degree.ind_on, simp,
     exact lt_jump _ } 

theorem djump_neq (d : 𝓓) : d ≠ d⁺ := λ h,
by { have : d⁺ ≤ d, rw ←h,
     exact (lt_djump d).2 this }

instance : nontrivial 𝓓 := ⟨⟨0, 0⁺, djump_neq 0⟩⟩

theorem nat_embedding : ℕ ↪o 𝓓 :=
begin
  split, swap,
  have : function.injective (djump_itr 0),
  { intros n m, contrapose, }
end

def incomparable (d₀ d₁ : 𝓓) := ¬d₀ ≤ d₁ ∧ ¬d₁ ≤ d₀

infix ` ∥ `:1200 := incomparable

theorem incomparable_degree_in_0' : ∃ d₀ d₁ : 𝓓,
  d₀ ≤ 0⁺ ∧ d₁ ≤ 0⁺ ∧ d₀ ∥ d₁ :=
by { rcases Kleene_Post.Kleene_Post with ⟨I₀, I₁, h⟩,
     refine ⟨deg I₀, deg I₁, _⟩,
     simp [has_zero.zero], exact h }

theorem intermediate_degree_in_0' : ∃ d : 𝓓,
  0 < d ∧ d < 0⁺ :=
begin
  rcases incomparable_degree_in_0' with ⟨d₀, d₁, hd₀, hd₁, incomp₀, incomp₁⟩,
  have : 0 < d₀ ∨ 0 < d₁,
  { by_contra C, 
    have : ¬0 < d₀ ∧ ¬0 < d₁, exact not_or_distrib.mp C,
    simp [has_lt.lt] at this, 
    have : d₀ ≤ d₁, from this.1.trans (by simp),
    contradiction },  
  by_contra C,
  simp at C,
  cases this,
  { have := C _ this,
    simp [has_lt.lt] at this,
    have : 0⁺ ≤ d₀ := this hd₀,
    have : d₁ ≤ d₀ := hd₁.trans this,
    contradiction },
  { have := C _ this,
    simp [has_lt.lt] at this,
    have : 0⁺ ≤ d₁ := this hd₁,
    have : d₀ ≤ d₁ := hd₀.trans this,
    contradiction }
end

theorem Friedberg_Muchnik' : ∃ d₀ d₁ : 𝓓,
  d₀ ∈ 𝓡 ∧ d₁ ∈ 𝓡 ∧ d₀ ∥ d₁ :=
by sorry

end turing_degree