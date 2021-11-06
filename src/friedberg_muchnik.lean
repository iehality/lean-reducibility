import its reducibility

open encodable denumerable

attribute [simp] set.set_of_app_iff

namespace friedberg_muchnik

def str : strategy 1 := default _

def generator : ℕ → (Tree 0 × (list ℕ × list ℕ))
| 0       := ([], [], [])
| (s + 1) :=
    let μ  : Tree 0 := (generator s).1, 
        I₀ : list ℕ := (generator s).2.1,
        I₁ : list ℕ := (generator s).2.2,
        η  : Tree 1 := str.up μ in
    match s.bodd with
    | ff := if ⟦η.length⟧ᵪ^I₀.chr [μ.weight] η.weight = some ff then (∞ :: μ, I₀, η.weight :: I₁) else (𝟘 :: μ, I₀, I₁)
    | tt := if ⟦η.length⟧ᵪ^I₁.chr [μ.weight] η.weight = some ff then (∞ :: μ, η.weight :: I₀, I₁) else (𝟘 :: μ, I₀, I₁)
    end

def Λ₀ : Path 0 := ⟨λ s, (generator s).fst, λ s,
  by { cases C : s.bodd; simp[generator, C],
       { by_cases C₁ : ⟦(up[str] (generator s).fst).length⟧ᵪ^((generator s).2.1.chr) [(generator s).1.weight]
         (up[str] (generator s).1).weight = some ff; simp[C₁] },
       { by_cases C₁ : ⟦(up[str] (generator s).fst).length⟧ᵪ^((generator s).2.2.chr) [(generator s).1.weight]
         (up[str] (generator s).1).weight = some ff; simp[C₁] } }⟩

lemma Λ₀_thick : Λ₀.thick :=
⟨by simp[Λ₀, generator], λ s, by { cases C : s.bodd; simp[Λ₀, generator, C],
  { by_cases C₁ : ⟦(up[str] (generator s).fst).length⟧ᵪ^((generator s).2.1.chr) [(generator s).1.weight]
      (up[str] (generator s).1).weight = some ff; simp[C₁], { refine ⟨_, rfl⟩ }, { refine ⟨_, rfl⟩ } },
  { by_cases C₁ : ⟦(up[str] (generator s).fst).length⟧ᵪ^((generator s).2.2.chr) [(generator s).1.weight]
      (up[str] (generator s).1).weight = some ff; simp[C₁], { refine ⟨_, rfl⟩ }, { refine ⟨_, rfl⟩ } } }⟩

lemma Λ₀_app_eq (s : ℕ) : Λ₀ s = (generator s).1 := rfl

def I₀ (s : ℕ) : list ℕ := (generator s).2.1

def I₁ (s : ℕ) : list ℕ := (generator s).2.2

def I₀_inf : set ℕ := {n | ∃ s, n ∈ I₀ s}

def I₁_inf : set ℕ := {n | ∃ s, n ∈ I₁ s}

@[reducible]
def directing_sentence₀ (s : ℕ) : Prop := ⟦(up[str] (Λ₀ s)).length⟧ᵪ^(I₀ s).chr [(Λ₀ s).weight] (up[str] (Λ₀ s)).weight = ff

@[reducible]
def directing_sentence₁ (s : ℕ) : Prop := ⟦(up[str] (Λ₀ s)).length⟧ᵪ^(I₁ s).chr [(Λ₀ s).weight] (up[str] (Λ₀ s)).weight = ff

lemma generator_eq_even_pi {s : ℕ} (even : s.bodd = ff) :
  directing_sentence₀ s → generator (s + 1) = (∞ :: Λ₀ s, I₀ s, (up[str] (Λ₀ s)).weight :: (I₁ s)) := λ C,
by { simp[directing_sentence₀, I₀, I₁, Λ₀_app_eq] at C, simp[generator, even, C, Λ₀_app_eq, I₀, I₁] }

lemma generator_eq_even_sigma {s : ℕ} (even : s.bodd = ff) :
  ¬directing_sentence₀ s → generator (s + 1) = (𝟘 :: Λ₀ s, I₀ s, I₁ s) := λ C,
by { simp[directing_sentence₀, I₀, I₁, Λ₀_app_eq] at C, simp[generator, even, C, Λ₀_app_eq, I₀, I₁], intros h, contradiction }

lemma pi_outcome_even {s} (pi : (Λ₀_thick.out s).is_pi) (even : s.bodd = ff) :
  ⟦(up[str] (Λ₀ s)).length⟧ᵪ^(I₀ s).chr [(Λ₀ s).weight] (up[str] (Λ₀ s)).weight = ff ∧
  (up[str] (Λ₀ s)).weight ∈ I₀ (s + 1):=
begin
  have := Λ₀_thick.succ_eq s,
  have : generator (s + 1) = (∞ :: Λ₀ s, I₀ s, (up[str] (Λ₀ s)).weight :: (I₁ s)),
  { simp[generator, even],
    by_cases C : ⟦(up[str] (generator s).1).length⟧ᵪ^((generator s).2.1.chr) [(generator s).1.weight]
    (up[str] (generator s).1).weight = some 𝟘; simp[C, Λ₀_app_eq, I₀, I₁],
    {  }
     }
end



end friedberg_muchnik
