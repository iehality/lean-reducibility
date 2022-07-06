import lib init.algebra.order

universes u v

namespace landau_natation

variables (α : Type u) [has_mul α] [linear_order α]

def eventually (p : ℕ → Prop) : Prop := ∃ n : ℕ, ∀ m ≥ n, p m

local notation `Eventually` binders `, ` r:(scoped p, eventually p) := r

def frequently (p : ℕ → Prop) : Prop := ∀ n : ℕ, ∃ m ≥ n, p m

local notation `Frequently` binders `, ` r:(scoped p, frequently p) := r


lemma eventually_def (p : ℕ → Prop) : (Eventually x, p x) ↔ (∃ n : ℕ, ∀ m ≥ n, p m) := by refl

lemma eventually_of_all (p : ℕ → Prop) (h : ∀ x, p x) : Eventually x, p x := ⟨0, λ m _, h m⟩

lemma eventually_and {p q : ℕ → Prop} : (Eventually x, p x ∧ q x) ↔ (Eventually x, p x) ∧ (Eventually x, q x) :=
⟨by { rintros ⟨M, h⟩, refine ⟨⟨M, λ m le, (h m le).left⟩, ⟨M, λ m le, (h m le).right⟩⟩,
 },
 by { rintros ⟨⟨M₁, h₁⟩, ⟨M₂, h₂⟩⟩, refine ⟨max M₁ M₂, _⟩, simp,
      intros m le₁ le₂, exact ⟨h₁ m le₁, h₂ m le₂⟩ }⟩

lemma eventually_imply {p q : ℕ → Prop} (I : ∀ x, p x → q x) : (Eventually x, p x) → (Eventually x, q x) :=
by rintros ⟨c, h⟩; refine ⟨c, λ m le, I _ (h m le)⟩

lemma frequently_def (p : ℕ → Prop) : (Frequently x, p x) ↔ (∀ n : ℕ, ∃ m ≥ n, p m) := by refl


def bigO (f : ℕ → ℕ) : set (ℕ → ℕ) := {g | ∃ c : ℕ , Eventually x, g x ≤ c * (f x)}

notation `O[` f `]` := bigO f

def bigO_symm (f g : ℕ → ℕ) : Prop := g ∈ O[f] ∧ f ∈ O[g]

infix ` ≃Θ `:60 := bigO_symm

notation `O[` f `]` := bigO f

lemma bigO_def (f g : ℕ → ℕ) : g ∈ O[f] ↔ ∃ c, Eventually x, g x ≤ c * (f x) := by refl

@[refl, simp] protected lemma refl {f : ℕ → ℕ} : f ∈ O[f] :=
⟨1, 0, λ m _, by simp⟩

@[trans] lemma trans {f g h : ℕ → ℕ} : 
  f ∈ O[g] → g ∈ O[h] → f ∈ O[h] :=
begin
  simp[bigO_def],
  intros c₁ h₁ c₂ h₂,
  refine ⟨c₁ * c₂, _⟩,
  have : (Eventually x, f x ≤ c₁ * g x ∧ g x ≤ c₂ * h x), refine eventually_and.mpr ⟨h₁, h₂⟩,
  refine eventually_imply _ this,
  { rintros x ⟨le₁, le₂⟩, 
    have : c₁ * g x ≤ c₁ * c₂ * h x, by simpa[mul_assoc] using mul_le_mul_left' le₂ c₁,
    exact le_trans le₁ this }
end

-- lemma mul_iff {f g : ℕ → ℕ} (k : ℕ) (hk : 0 ≠ k) : O[f] (λ x, k * g x) ↔ O[f] g :=
-- ⟨by { rintros ⟨c, h⟩, refine ⟨c, eventually_imply (λ x, _) h⟩, simp,  }, by {  }⟩



end landau_natation