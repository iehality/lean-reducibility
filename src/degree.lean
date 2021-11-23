import reducibility friedberg_muchnik
open encodable denumerable part

-- Degrees of Unsolvability

attribute [instance, priority 0] classical.prop_decidable

@[notation_class] class has_jump (α : Type*) := (jump : α → α)

postfix `⁺`:(max+1) := has_jump.jump

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

@[simp] lemma of_le_of {A B} : deg A ≤ deg B ↔ A ≤ₜ B := by refl

instance : semilattice_sup_bot 𝐃 :=
{ le := (≤),
  sup := λ a b, turing_degree.lift_on₂ a b (λ A B, deg (Join₂ A B)) (λ A₁ B₁ A₂ B₂ hA hB,
   by { simp, split,
        { have lmm₁ : A₁ ≤ₜ Join₂ A₂ B₂, from hA.1.trans (le_Join₂_left _ _).to_turing,
          have lmm₂ : B₁ ≤ₜ Join₂ A₂ B₂, from hB.1.trans (le_Join₂_right _ _).to_turing,
          refine Join₂_le A₁ B₁ _ lmm₁ lmm₂ },
        { have lmm₁ : A₂ ≤ₜ Join₂ A₁ B₁, from hA.2.trans (le_Join₂_left _ _).to_turing,
          have lmm₂ : B₂ ≤ₜ Join₂ A₁ B₁, from hB.2.trans (le_Join₂_right _ _).to_turing,
          refine Join₂_le A₂ B₂ _ lmm₁ lmm₂ } }),
  bot := deg ∅,
  le_refl := λ d, by induction d using turing_degree.ind_on; simp,
  le_trans := λ a b c,
  by { induction a using turing_degree.ind_on,
       induction b using turing_degree.ind_on,
       induction c using turing_degree.ind_on,
       exact t_reducible.trans },
  le_antisymm := λ a b,
  by { induction a using turing_degree.ind_on,
       induction b using turing_degree.ind_on,
       intros hp hq,
       simp only [*, t_reducible_equiv, of_le_of, of_eq_of, true_and] at * },
  le_sup_left := λ a b,
  by { induction a using turing_degree.ind_on,
       induction b using turing_degree.ind_on,
       simp[has_sup.sup], exact (le_Join₂_left _ _).to_turing },
  le_sup_right := λ a b,
  by { induction a using turing_degree.ind_on,
       induction b using turing_degree.ind_on,
       simp[has_sup.sup], exact (le_Join₂_right _ _).to_turing },
  sup_le := λ a b c,
  by { induction a using turing_degree.ind_on,
       induction b using turing_degree.ind_on,
       induction c using turing_degree.ind_on,
       simp[has_sup.sup], exact Join₂_le a b c },
  bot_le := λ a, by { induction a using turing_degree.ind_on, simp, exact computable_le _ computable_0 } }

lemma of_sup_of {A B} : deg A ⊔ deg B = deg (Join₂ A B) := rfl

instance : inhabited 𝐃 := ⟨⊥⟩

def djump : 𝐃 → 𝐃 :=
λ d, turing_degree.lift_on d (λ d, deg d′)
(λ A B ⟨ab, ba⟩, by { simp, exact 
 ⟨(le_le_Jump ab).to_many_one.to_turing, (le_le_Jump ba).to_many_one.to_turing⟩ })

instance : has_jump 𝐃 := ⟨djump⟩

def djump_itr (d : 𝐃) : ℕ → 𝐃
| 0     := d
| (n+1) := (djump_itr n)⁺

@[simp] lemma of_jump {A} : (deg A)⁺ = deg A′ := rfl

def re_degree := {d // ∃ R : set ℕ, r.e. R ∧ d = deg R}

notation `𝐑` := re_degree

instance : has_coe 𝐑 𝐃 := ⟨subtype.val⟩

instance : semilattice_sup_bot 𝐑 :=
  { le := λ a b, (a : 𝐃) ≤ (b : 𝐃),
    sup := λ a b, ⟨(a : 𝐃) ⊔ (b : 𝐃),
      by { rcases a with ⟨a, A, reA, rfl⟩, rcases b with ⟨b, B, reB, rfl⟩,
           refine ⟨Join₂ A B, re_Join_of_re_re reA reB, by simp[of_sup_of]⟩ }⟩,
    bot := ⟨⊥, ∅, re_pred_0, rfl⟩,
    le_refl := by simp,
    le_trans := λ ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, by {simp, exact le_trans },
    le_antisymm := λ ⟨a, _⟩ ⟨b, _⟩, by { simp, exact le_antisymm },
    bot_le := λ ⟨a, _⟩, by simp,
    le_sup_left := λ ⟨a, _⟩ ⟨b, _⟩, by simp,
    le_sup_right := λ ⟨a, _⟩ ⟨b, _⟩, by simp,
    sup_le := λ ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, by { simp[-sup_le_iff], exact sup_le } }

instance : semilattice_sup_top 𝐑 :=
  { top := ⟨⊥⁺, (∅ : set ℕ)′, re_pred_Jump_0, rfl⟩,
    le_top := λ ⟨a, R, reR, rfl⟩, by { simp[has_top.top, show ⊥⁺ = deg ∅′, by refl],
    exact (re_many_one_reducible_to_0'.mp reR).to_turing },
    ..re_degree.semilattice_sup_bot }

def High := {d : 𝐑 | (d : 𝐃)⁺ = ⊥⁺⁺}

def Low  := {d : 𝐑 | (d : 𝐃)⁺ = ⊥⁺}

@[simp] lemma of_lt_of {A B} : deg A < deg B ↔ A <ₜ B := by refl

theorem lt_djump (d : 𝐃) : d < d⁺ :=
by { induction d using turing_degree.ind_on, simp,
     exact lt_Jump _ } 

theorem djump_neq (d : 𝐃) : d ≠ d⁺ := λ h,
by { have : d⁺ ≤ d, rw ←h,
     exact (lt_djump d).2 this }

instance : nontrivial 𝐃 := ⟨⟨⊥, ⊥⁺, djump_neq ⊥⟩⟩

lemma jump_order_preserving (a b : 𝐃) (le : a ≤ b) : a⁺ ≤ b⁺ :=
by { induction a using turing_degree.ind_on,
     induction b using turing_degree.ind_on,
     simp at le ⊢, exact (le_le_Jump le).to_turing }

theorem friedberg_muchnik : ∃ a b : 𝐑, ¬a ≤ b ∧ ¬b ≤ a :=
by rcases friedberg_muchnik.incomparable_re_sets with ⟨I₀, I₁, re₀, re₁, nle₀, nle₁⟩;
   refine ⟨⟨deg I₀, I₀, re₀, rfl⟩, ⟨deg I₁, I₁, re₁, rfl⟩, nle₁, nle₀⟩

end turing_degree