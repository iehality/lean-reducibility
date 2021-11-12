import reducibility friedberg_muchnik
open encodable denumerable part

local attribute [instance, priority 0] classical.prop_decidable

theorem equivalence_of_t_reducible_equiv (α) [primcodable α] :
  equivalence (@t_reducible_equiv α α _ _) :=
⟨λ x, t_reducible_equiv.refl x,
 λ _ _, t_reducible_equiv.symm,
 λ _ _ _, t_reducible_equiv.trans⟩

def turing_degree : Type :=
quotient (⟨t_reducible_equiv, equivalence_of_t_reducible_equiv ℕ⟩ : setoid (set ℕ))

notation `𝐃` := turing_degree

namespace turing_degree

def deg (A : set ℕ) : 𝐃 := quotient.mk' A

@[elab_as_eliminator]
protected lemma ind_on {C : 𝐃 → Prop} (d : 𝐃)
  (h : ∀ p : set ℕ, C (deg p)) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : 𝐃) (f : set ℕ → φ)
  (h : ∀ p q, p ≡ₜ q → f p = f q) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (p : set ℕ) (f : set ℕ → φ)
  (h : ∀ p q, t_reducible_equiv p q → f p = f q) : (deg p).lift_on f h = f p :=
rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : 𝐃) (f : set ℕ → set ℕ → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ≡ₜ q₁ → p₂ ≡ₜ q₂ → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (p q : set ℕ) (f : set ℕ → set ℕ → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ≡ₜ q₁ → p₂ ≡ₜ q₂ → f p₁ p₂ = f q₁ q₂) :
  (deg p).lift_on₂ (deg q) f h = f p q := rfl

@[simp] lemma of_eq_of {p q} : deg p = deg q ↔ p ≡ₜ q :=
by simp [deg, quotient.eq']

instance : has_le 𝐃 :=
⟨λ d₁ d₂, turing_degree.lift_on₂ d₁ d₂ (≤ₜ) $
 λ p₁ p₂ q₁ q₂ hp hq, propext 
 ⟨λ hpq, (hp.2.trans hpq).trans hq.1, λ hpq, (hp.1.trans hpq).trans hq.2⟩⟩

instance : has_lt 𝐃 := ⟨λ d₀ d₁, d₀ ≤ d₁ ∧ ¬d₁ ≤ d₀⟩

instance : has_zero 𝐃 := ⟨deg (∅ : set ℕ)⟩

instance : inhabited 𝐃 := ⟨0⟩

def djump : 𝐃 → 𝐃 :=
λ d, turing_degree.lift_on d (λ d, deg d′)
(λ A B ⟨ab, ba⟩, by { simp, exact 
 ⟨(le_le_Jump ab).to_many_one.to_turing, (le_le_Jump ba).to_many_one.to_turing⟩ })

notation d`⁺`:1200 := djump d

def djump_itr (d : 𝐃) : ℕ → 𝐃
| 0     := d
| (n+1) := (djump_itr n)⁺

@[simp] lemma of_le_of {A B} : deg A ≤ deg B ↔ A ≤ₜ B := by refl

@[simp] lemma of_lt_of {A B} : deg A < deg B ↔ A <ₜ B := by refl

@[simp] lemma of_jump {A} : (deg A)⁺ = deg A′ := by refl

@[simp] theorem zero_minimum (d : 𝐃) : 0 ≤ d :=
by { induction d using turing_degree.ind_on, simp [has_zero.zero],
     exact computable_le d computable_0 }

def RE_degree := {d | ∃ R : set ℕ, r.e. R ∧ d = deg R}

notation `𝐑` := RE_degree

def High := {d | d ∈ 𝐑 ∧ d⁺ = 0⁺⁺}

def Low  := {d | d ∈ 𝐑 ∧ d⁺ = 0⁺}

private lemma le_refl (d : 𝐃) : d ≤ d :=
by induction d using turing_degree.ind_on; simp

private lemma le_antisymm {d₁ d₂ : 𝐃} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ :=
begin
  induction d₁ using turing_degree.ind_on,
  induction d₂ using turing_degree.ind_on,
  intros hp hq,
  simp only [*, t_reducible_equiv, of_le_of, of_eq_of, true_and] at *
end

private lemma le_trans {d₁ d₂ d₃ : 𝐃} :
  d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ :=
begin
  induction d₁ using turing_degree.ind_on,
  induction d₂ using turing_degree.ind_on,
  induction d₃ using turing_degree.ind_on,
  exact t_reducible.trans
end

instance : partial_order 𝐃 :=
{ le := (≤),
  le_refl := le_refl,
  le_trans := λ _ _ _, le_trans,
  le_antisymm := λ _ _, le_antisymm }

theorem lt_djump (d : 𝐃) : d < d⁺ :=
by { induction d using turing_degree.ind_on, simp,
     exact lt_Jump _ } 

theorem djump_neq (d : 𝐃) : d ≠ d⁺ := λ h,
by { have : d⁺ ≤ d, rw ←h,
     exact (lt_djump d).2 this }

instance : nontrivial 𝐃 := ⟨⟨0, 0⁺, djump_neq 0⟩⟩

theorem friedberg_muchnik : ∃ d₀ d₁ : 𝐑, ¬d₀ ≤ d₁ ∧ ¬d₁ ≤ d₀ :=
by rcases friedberg_muchnik.incomparable_re_sets with ⟨I₀, I₁, re₀, re₁, nle₀, nle₁⟩;
   refine ⟨⟨deg I₀, I₀, re₀, rfl⟩, ⟨deg I₁, I₁, re₁, rfl⟩, nle₁, nle₀⟩

end turing_degree