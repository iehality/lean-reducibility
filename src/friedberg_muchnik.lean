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
        η  : Tree 1 := up[str] μ in
    match η.length.bodd with
    | ff := if ⟦η.length.div2⟧ᵪ^I₀.chr [(λ[str] μ).weight] η.weight = some ff then (∞ :: μ, I₀, η.weight :: I₁) else (𝟘 :: μ, I₀, I₁)
    | tt := if ⟦η.length.div2⟧ᵪ^I₁.chr [(λ[str] μ).weight] η.weight = some ff then (∞ :: μ, η.weight :: I₀, I₁) else (𝟘 :: μ, I₀, I₁)
    end

def Λ : Path 0 := ⟨λ s, (generator s).fst, λ s,
  by { cases C : (up[str] (generator s).1).length.bodd; simp[generator, C],
       { by_cases C₁ : ⟦(up[str] (generator s).1).length.div2⟧ᵪ^((generator s).2.1.chr) [(λ[str] (generator s).1).weight]
         (up[str] (generator s).1).weight = some ff; simp[C₁] },
       { by_cases C₁ : ⟦(up[str] (generator s).1).length.div2⟧ᵪ^((generator s).2.2.chr) [(λ[str] (generator s).1).weight]
         (up[str] (generator s).1).weight = some ff; simp[C₁] } }⟩

lemma Λ_thick : Λ.thick :=
⟨by simp[Λ, generator], λ s, by { cases C : (up[str] (generator s).1).length.bodd; simp[Λ, generator, C],
  { by_cases C₁ : ⟦(up[str] (generator s).1).length.div2⟧ᵪ^((generator s).2.1.chr) [(λ[str] (generator s).1).weight]
         (up[str] (generator s).1).weight = some ff; simp[C₁], { refine ⟨_, rfl⟩ }, { refine ⟨_, rfl⟩ } },
  { by_cases C₁ : ⟦(up[str] (generator s).1).length.div2⟧ᵪ^((generator s).2.2.chr) [(λ[str] (generator s).1).weight]
         (up[str] (generator s).1).weight = some ff; simp[C₁], { refine ⟨_, rfl⟩ }, { refine ⟨_, rfl⟩ } } }⟩

lemma Λ_app_eq (s : ℕ) : Λ s = (generator s).1 := rfl

@[simp] lemma Λ_empty : Λ 0 = [] := rfl

def I₀ (s : ℕ) : list ℕ := (generator s).2.1

@[simp] lemma I₀_empty : I₀ 0 = [] := rfl

def I₁ (s : ℕ) : list ℕ := (generator s).2.2

@[simp] lemma I₁_empty : I₁ 0 = [] := rfl

def I₀_inf : set ℕ := {n | ∃ s, n ∈ I₀ s}

def I₁_inf : set ℕ := {n | ∃ s, n ∈ I₁ s}

@[reducible]
def directing_sentence₀ (s : ℕ) : Prop :=
⟦(up[str] (Λ s)).length.div2⟧ᵪ^(I₀ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff

@[reducible]
def directing_sentence₁ (s : ℕ) : Prop :=
⟦(up[str] (Λ s)).length.div2⟧ᵪ^(I₁ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff

lemma generator_eq_of_pi_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) :
  directing_sentence₀ s → generator (s + 1) = (∞ :: Λ s, I₀ s, (up[str] (Λ s)).weight :: I₁ s) := λ C,
by { simp[directing_sentence₀, I₀, I₁, Λ_app_eq] at C even, simp[generator, even, C, Λ_app_eq, I₀, I₁] }

lemma generator_eq_of_sigma_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) :
  ¬directing_sentence₀ s → generator (s + 1) = (𝟘 :: Λ s, I₀ s, I₁ s) := λ C,
by { simp[directing_sentence₀, I₀, I₁, Λ_app_eq] at C even, simp[generator, even, C, Λ_app_eq, I₀, I₁], intros h, contradiction }

lemma generator_eq_of_pi_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) :
  directing_sentence₁ s → generator (s + 1) = (∞ :: Λ s, (up[str] (Λ s)).weight :: I₀ s, I₁ s) := λ C,
by { simp[directing_sentence₁, I₀, I₁, Λ_app_eq] at C odd, simp[generator, odd, C, Λ_app_eq, I₀, I₁] }

lemma generator_eq_of_sigma_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) :
  ¬directing_sentence₁ s → generator (s + 1) = (𝟘 :: Λ s, I₀ s, I₁ s) := λ C,
by { simp[directing_sentence₁, I₀, I₁, Λ_app_eq] at C odd, simp[generator, odd, C, Λ_app_eq, I₀, I₁], intros h, contradiction }

lemma I₁_eq_of_pi_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) :
  directing_sentence₀ s → I₁ (s + 1) = (up[str] (Λ s)).weight :: I₁ s := λ C,
by simp[I₁, generator_eq_of_pi_of_even even C]

lemma I₁_eq_of_sigma_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) :
  ¬directing_sentence₀ s → I₁ (s + 1) = I₁ s := λ C,
by simp[I₁, generator_eq_of_sigma_of_even even C]

lemma I₀_eq_of_pi_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) :
  directing_sentence₁ s → I₀ (s + 1) = (up[str] (Λ s)).weight :: I₀ s := λ C,
by simp[I₀, generator_eq_of_pi_of_odd odd C]

lemma I₀_eq_of_sigma_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) :
  ¬directing_sentence₁ s → I₀ (s + 1) = I₀ s := λ C,
by simp[I₀, generator_eq_of_sigma_of_odd odd C]

@[simp] lemma I₁_eq_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) : I₁ (s + 1) = I₁ s :=
by { by_cases C : directing_sentence₁ s,
     simp[I₁, generator_eq_of_pi_of_odd odd C], simp[I₁, generator_eq_of_sigma_of_odd odd C] }

@[simp] lemma I₀_eq_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) : I₀ (s + 1) = I₀ s :=
by { by_cases C : directing_sentence₀ s,
     simp[I₀, generator_eq_of_pi_of_even even C], simp[I₀, generator_eq_of_sigma_of_even even C] }

lemma mem_I₁_inf_of_pi_of_even {s} (even : (up[str] (Λ s)).length.bodd = ff) (pi : directing_sentence₀ s) :
  (up[str] (Λ s)).weight ∈ I₁_inf := ⟨s + 1, by simp[I₁_eq_of_pi_of_even even pi]⟩

lemma mem_I₀_inf_of_pi_of_odd {s} (odd : (up[str] (Λ s)).length.bodd = tt) (pi : directing_sentence₁ s) :
  (up[str] (Λ s)).weight ∈ I₀_inf := ⟨s + 1, by simp[I₀_eq_of_pi_of_odd odd pi]⟩

lemma mem_I₁_iff (t a : ℕ) :
  a ∈ I₁ t ↔ ∃ s < t, (up[str] (Λ s)).length.bodd = ff ∧ a = (up[str] (Λ s)).weight ∧ directing_sentence₀ s :=
begin
  induction t with t IH,
  { simp },
  { rcases C : (up[str] (Λ t)).length.bodd with (C | C),
    { by_cases C₂ : directing_sentence₀ t,
      { simp[I₁_eq_of_pi_of_even C C₂, IH], split,
        { rintros (rfl | ⟨s, lt, s_even, rfl, pi⟩),
          { exact ⟨t, lt_add_one t, C, rfl, C₂⟩ }, { refine ⟨s, nat.lt.step lt, s_even, rfl, pi⟩ } },
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
          have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
          rcases this with (lt | rfl), { right, refine ⟨s, lt, s_even, rfl, pi⟩ }, { left, simp } } },
      { simp[I₁_eq_of_sigma_of_even C C₂, IH], split,
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩, refine ⟨s, nat.lt.step lt_s, s_even, rfl, pi⟩ },
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
          have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
          rcases this with (lt | rfl), { refine ⟨s, lt, s_even, rfl, pi⟩ }, { exfalso, contradiction } } } },
    { simp[I₁_eq_of_odd C, IH], split,
      { rintros ⟨s, lt_s, s_even, rfl, pi⟩, refine ⟨s, nat.lt.step lt_s, s_even, rfl, pi⟩ },
      { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
        have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
        rcases this with (lt | rfl),
        { refine ⟨s, lt, s_even, rfl, pi⟩ }, { exfalso, simp[C] at s_even, contradiction } } } }
end

lemma mem_I₀_iff (t a : ℕ) :
  a ∈ I₀ t ↔ ∃ s < t, (up[str] (Λ s)).length.bodd = tt ∧ a = (up[str] (Λ s)).weight ∧ directing_sentence₁ s :=
begin
  induction t with t IH,
  { simp },
  { rcases C : (up[str] (Λ t)).length.bodd with (C | C),
    { simp[I₀_eq_of_even C, IH], split,
      { rintros ⟨s, lt_s, s_even, rfl, pi⟩, refine ⟨s, nat.lt.step lt_s, s_even, rfl, pi⟩ },
      { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
        have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
        rcases this with (lt | rfl),
        { refine ⟨s, lt, s_even, rfl, pi⟩ }, { exfalso, simp[C] at s_even, contradiction } } },
    { by_cases C₂ : directing_sentence₁ t,
      { simp[I₀_eq_of_pi_of_odd C C₂, IH], split,
        { rintros (rfl | ⟨s, lt, s_even, rfl, pi⟩),
          { exact ⟨t, lt_add_one t, C, rfl, C₂⟩ }, { refine ⟨s, nat.lt.step lt, s_even, rfl, pi⟩ } },
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
          have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
          rcases this with (lt | rfl), { right, refine ⟨s, lt, s_even, rfl, pi⟩ }, { left, simp } } },
      { simp[I₀_eq_of_sigma_of_odd C C₂, IH], split,
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩, refine ⟨s, nat.lt.step lt_s, s_even, rfl, pi⟩ },
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
          have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
          rcases this with (lt | rfl), { refine ⟨s, lt, s_even, rfl, pi⟩ }, { exfalso, contradiction } } } } }
end

lemma I₁_mono {s₁ s₂ : ℕ} (le : s₁ ≤ s₂) : I₁ s₁ ⊆ I₁ s₂ := λ a mem,
by { simp [mem_I₁_iff] at mem ⊢, rcases mem with ⟨s, lt_s, h⟩, refine ⟨s, gt_of_ge_of_gt le lt_s, h⟩ }

lemma I₀_mono {s₁ s₂ : ℕ} (le : s₁ ≤ s₂) : I₀ s₁ ⊆ I₀ s₂ := λ a mem,
by { simp [mem_I₀_iff] at mem ⊢, rcases mem with ⟨s, lt_s, h⟩, refine ⟨s, gt_of_ge_of_gt le lt_s, h⟩ }

@[simp] lemma pi_outcome_iff_of_even {s} (even : (up[str] (Λ s)).length.bodd = ff) :
  (Λ_thick.out s).is_pi ↔ directing_sentence₀ s :=
begin
  by_cases C : directing_sentence₀ s; simp[C],
  { have : (Λ (s + 1)).is_sigma, { simp[Λ_app_eq, generator_eq_of_pi_of_even even C] },
    simp[Λ_thick.succ_eq s] at this, exact this },
  { have : (Λ (s + 1)).is_pi, { simp[Λ_app_eq, generator_eq_of_sigma_of_even even C] },
    simp[Λ_thick.succ_eq s] at this, simp[this, infinity, zero] }
end

@[simp] lemma sigma_outcome_iff_of_even {s} (even : (up[str] (Λ s)).length.bodd = ff) :
  (Λ_thick.out s).is_sigma ↔ ¬directing_sentence₀ s :=
by { simp[←pi_outcome_iff_of_even even], cases Λ_thick.out s; simp[infinity, zero] }

@[simp] lemma pi_outcome_iff_of_odd {s} (odd : (up[str] (Λ s)).length.bodd = tt) :
  (Λ_thick.out s).is_pi ↔ directing_sentence₁ s :=
begin
  by_cases C : directing_sentence₁ s; simp[C],
  { have : (Λ (s + 1)).is_sigma, { simp[Λ_app_eq, generator_eq_of_pi_of_odd odd C] },
    simp[Λ_thick.succ_eq s] at this, exact this },
  { have : (Λ (s + 1)).is_pi, { simp[Λ_app_eq, generator_eq_of_sigma_of_odd odd C] },
    simp[Λ_thick.succ_eq s] at this, simp[this, infinity, zero] }
end

@[simp] lemma sigma_outcome_iff_of_odd {s} (odd : (up[str] (Λ s)).length.bodd = tt) :
  (Λ_thick.out s).is_sigma ↔ ¬directing_sentence₁ s :=
by { simp[←pi_outcome_iff_of_odd odd], cases Λ_thick.out s; simp[infinity, zero] }

lemma sigma_preservation_of_pi_of_even
  {s₁ s₂} (even : (up[str] (Λ s₁)).length.bodd = ff) (pi : directing_sentence₀ s₁) 
  (on_truepath : up[str] (Λ s₁) ⊆' Λ[str] Λ) (le : s₁ ≤ s₂) {a : ℕ} (bound : a ≤ (λ[str] (Λ s₁)).weight) :
  a ∈ I₀ s₂ → a ∈ I₀ s₁ :=
begin
  simp only [mem_I₀_iff],
  rintros ⟨s, lt_s, odd, rfl, pi_s⟩,
  have : s < s₁ ∨ s = s₁ ∨ s₁ < s, exact trichotomous s s₁, rcases this with (lt_s | lt_s),
  { refine ⟨s, lt_s, odd, rfl, pi_s⟩ },
  exfalso,
  { rcases lt_s with (rfl | gt_s), { simp [odd] at even, contradiction },
    have : (λ[str] (Λ s₁)).weight < (up[str] (Λ s)).weight,
      from str.lt_weight_lambda_up Λ_thick (by simp) gt_s (by simp[even, pi]) (by simp[odd, pi_s]) on_truepath,
    exact nat.lt_le_antisymm this bound }
end

lemma sigma_preservation_of_even_aux
  {η : Tree 1} {s₀} {lt : η ⊂ᵢ (Λ[str] Λ) s₀} (sigma : (out ⟨η, lt⟩).is_sigma) (even : η.length.bodd = ff) :
  ∃ s, directing_sentence₀ s ∧
    up[str] (Λ s) = η ∧ ⟦η.length.div2⟧ᵪ^(chr I₀_inf) [(λ[str] (Λ s)).weight] η.weight = ff :=
begin
  rcases str.Lambda_sigma_outcome_of_thick Λ Λ_thick lt sigma with ⟨s, rfl, eq_out, pi⟩,
  have pi : directing_sentence₀ s, from (pi_outcome_iff_of_even even).mp pi,
  have : ∀ a : ℕ, a < (λ[str] (Λ s)).weight → (I₀ s).chr a = chr I₀_inf a,
  { intros a bound, simp[←bool.coe_bool_iff],
    show a ∈ I₀ s ↔ I₀_inf a,
    refine ⟨λ h, ⟨s, h⟩, λ ⟨t, h⟩, sigma_preservation_of_pi_of_even
      even pi ⟨s₀, lt.suffix⟩ (le_max_left s t) (le_of_lt bound) (I₀_mono (le_max_right s t) h)⟩ },
  have : ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(I₀ s).chr [(λ[str] (Λ s)).weight] =
    ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(chr I₀_inf) [(λ[str] (Λ s)).weight],
    from rpartrec.univn_tot_use this,
  refine ⟨s, pi, rfl, _⟩,  
  simp[←this], exact pi
end

lemma sigma_preservation_of_even
  {η : Tree 1} {s₀} {lt : η ⊂ᵢ (Λ[str] Λ) s₀} (sigma : (out ⟨η, lt⟩).is_sigma) (even : η.length.bodd = ff) :
  η.weight ∈ I₁_inf ∧ ff ∈ ⟦η.length.div2⟧ᵪ^(chr I₀_inf) η.weight :=
by { rcases sigma_preservation_of_even_aux sigma even with ⟨s, pi, rfl, eqn⟩,
     simp[rpartrec.univn_complete],
     refine ⟨mem_I₁_inf_of_pi_of_even even pi, (λ[str] (Λ s)).weight, eqn⟩}

lemma sigma_preservation_of_pi_of_odd
  {s₁ s₂} (odd : (up[str] (Λ s₁)).length.bodd = tt) (pi : directing_sentence₁ s₁) 
  (on_truepath : up[str] (Λ s₁) ⊆' Λ[str] Λ) (le : s₁ ≤ s₂) {a : ℕ} (bound : a ≤ (λ[str] (Λ s₁)).weight) :
  a ∈ I₁ s₂ → a ∈ I₁ s₁:=
begin
  simp only [mem_I₁_iff],
  rintros ⟨s, lt_s, even, rfl, pi_s⟩,
  have : s < s₁ ∨ s = s₁ ∨ s₁ < s, exact trichotomous s s₁, rcases this with (lt_s | lt_s),
  { refine ⟨s, lt_s, even, rfl, pi_s⟩ },
  exfalso,
  { rcases lt_s with (rfl | gt_s), { simp [even] at odd, contradiction },
    have : (λ[str] (Λ s₁)).weight < (up[str] (Λ s)).weight,
      from str.lt_weight_lambda_up Λ_thick (by simp) gt_s (by simp[odd, pi]) (by simp[even, pi_s]) on_truepath,
    exact nat.lt_le_antisymm this bound }
end

lemma sigma_preservation_of_odd_aux
  {η : Tree 1} {s₀} {lt : η ⊂ᵢ (Λ[str] Λ) s₀} (sigma : (out ⟨η, lt⟩).is_sigma) (odd : η.length.bodd = tt) :
  ∃ s, directing_sentence₁ s ∧
    up[str] (Λ s) = η ∧ ⟦η.length.div2⟧ᵪ^(chr I₁_inf) [(λ[str] (Λ s)).weight] η.weight = ff :=
begin
  rcases str.Lambda_sigma_outcome_of_thick Λ Λ_thick lt sigma with ⟨s, rfl, eq_out, pi⟩,
  have pi : directing_sentence₁ s, from (pi_outcome_iff_of_odd odd).mp pi,
  have : ∀ a : ℕ, a < (λ[str] (Λ s)).weight → (I₁ s).chr a = chr I₁_inf a,
  { intros a bound, simp[←bool.coe_bool_iff],
    show a ∈ I₁ s ↔ I₁_inf a,
    refine ⟨λ h, ⟨s, h⟩, λ ⟨t, h⟩, sigma_preservation_of_pi_of_odd
      odd pi ⟨s₀, lt.suffix⟩ (le_max_left s t) (le_of_lt bound) (I₁_mono (le_max_right s t) h)⟩ },
  have : ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(I₁ s).chr [(λ[str] (Λ s)).weight] =
    ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(chr I₁_inf) [(λ[str] (Λ s)).weight],
    from rpartrec.univn_tot_use this,
  refine ⟨s, pi, rfl, _⟩,  
  simp[←this], exact pi
end

lemma sigma_preservation_of_odd
  {η : Tree 1} {s₀} {lt : η ⊂ᵢ (Λ[str] Λ) s₀} (sigma : (out ⟨η, lt⟩).is_sigma) (odd : η.length.bodd = tt) :
  η.weight ∈ I₀_inf ∧ ff ∈ ⟦η.length.div2⟧ᵪ^(chr I₁_inf) η.weight :=
by { rcases sigma_preservation_of_odd_aux sigma odd with ⟨s, pi, rfl, eqn⟩,
     simp[rpartrec.univn_complete],
     refine ⟨mem_I₀_inf_of_pi_of_odd odd pi, (λ[str] (Λ s)).weight, eqn⟩ }

lemma nonmem_of_even
  {η : Tree 1} {t} {lt : η ⊂ᵢ (Λ[str] Λ) t} (pi : (out ⟨η, lt⟩).is_pi) (even : η.length.bodd = ff) :
  η.weight ∉ I₁_inf := λ mem,
begin
  rcases mem with ⟨s₀, mem⟩,
  rcases (mem_I₁_iff s₀ η.weight).mp mem with ⟨s, lt_s, _, eq_weight, pi⟩,
  have : η = up[str] (Λ s),
  { rcases str.le_Lambda_of_thick' Λ_thick ⟨t, lt.suffix⟩ with ⟨s₀, rfl, _⟩, simp at*,
    rcases str.eq_lambda_of_le_lambda' (str.up_le_lambda (Λ s)) with ⟨μ₀, le_μ₀, eq_up⟩,
    rcases Λ_thick.ssubset.mp ⟨s, le_μ₀⟩ with ⟨s', rfl⟩,
    simp[eq_up] at eq_weight ⊢, exact str.weight_lambda_inj_of_thick Λ_thick eq_weight },
  rcases this with rfl,
  have : ¬directing_sentence₀ s, from (sigma_outcome_iff_of_even even).mp (str.Lambda_pi_outcome_of_thick Λ_thick pi s rfl),
  contradiction
end

lemma nonmem_of_odd
  {η : Tree 1} {t} {lt : η ⊂ᵢ (Λ[str] Λ) t} (pi : (out ⟨η, lt⟩).is_pi) (odd : η.length.bodd = tt) :
  η.weight ∉ I₀_inf := λ mem,
begin
  rcases mem with ⟨s₀, mem⟩,
  rcases (mem_I₀_iff s₀ η.weight).mp mem with ⟨s, lt_s, _, eq_weight, pi⟩,
  have : η = up[str] (Λ s),
  { rcases str.le_Lambda_of_thick' Λ_thick ⟨t, lt.suffix⟩ with ⟨s₀, rfl, _⟩, simp at*,
    rcases str.eq_lambda_of_le_lambda' (str.up_le_lambda (Λ s)) with ⟨μ₀, le_μ₀, eq_up⟩,
    rcases Λ_thick.ssubset.mp ⟨s, le_μ₀⟩ with ⟨s', rfl⟩,
    simp[eq_up] at eq_weight ⊢, exact str.weight_lambda_inj_of_thick Λ_thick eq_weight },
  rcases this with rfl,
  have : ¬directing_sentence₁ s, from (sigma_outcome_iff_of_odd odd).mp (str.Lambda_pi_outcome_of_thick Λ_thick pi s rfl),
  contradiction
end

lemma I₀_beq_exists(b : ℕ) :
  ∃ s, ∀ a < b, a ∈ I₀ s ↔ a ∈ I₀_inf :=
begin
  induction b with b IH,
  { simp },
  { rcases IH with ⟨s₀, beq⟩,
    by_cases C : b ∈ I₀_inf,
    { rcases C with ⟨s_b, mem⟩,
      refine ⟨max s₀ s_b, λ a bound, _⟩,
      split, { intros mem, refine ⟨_, mem⟩ },
      intros mem,
      have : a < b ∨ a = b, from lt_or_eq_of_le (nat.lt_succ_iff.mp bound),
      rcases this with (lt | rfl),
      { have : a ∈ I₀ s₀, from (beq a lt).mpr mem, exact I₀_mono (le_max_left s₀ s_b) this },
      { exact I₀_mono (le_max_right s₀ s_b) mem } },
    { refine ⟨s₀, λ a bound, _⟩,
      have : a < b ∨ a = b, from lt_or_eq_of_le (nat.lt_succ_iff.mp bound),
      rcases this with (lt | rfl),
      { exact beq a lt },
      { simp[C], intros mem, have : a ∈ I₀_inf, from ⟨s₀, mem⟩, contradiction } } }
end

lemma I₁_beq_exists(b : ℕ) :
  ∃ s, ∀ a < b, a ∈ I₁ s ↔ a ∈ I₁_inf :=
begin
  induction b with b IH,
  { simp },
  { rcases IH with ⟨s₀, beq⟩,
    by_cases C : b ∈ I₁_inf,
    { rcases C with ⟨s_b, mem⟩,
      refine ⟨max s₀ s_b, λ a bound, _⟩,
      split, { intros mem, refine ⟨_, mem⟩ },
      intros mem,
      have : a < b ∨ a = b, from lt_or_eq_of_le (nat.lt_succ_iff.mp bound),
      rcases this with (lt | rfl),
      { have : a ∈ I₁ s₀, from (beq a lt).mpr mem, exact I₁_mono (le_max_left s₀ s_b) this },
      { exact I₁_mono (le_max_right s₀ s_b) mem } },
    { refine ⟨s₀, λ a bound, _⟩,
      have : a < b ∨ a = b, from lt_or_eq_of_le (nat.lt_succ_iff.mp bound),
      rcases this with (lt | rfl),
      { exact beq a lt },
      { simp[C], intros mem, have : a ∈ I₁_inf, from ⟨s₀, mem⟩, contradiction } } }
end

lemma pi_substrategies_of_even_aux
  {η : Tree 1} {t} {lt : η ⊂ᵢ (Λ[str] Λ) t} (pi : (out ⟨η, lt⟩).is_pi) (even : η.length.bodd = ff) :
  ∀ s₀ : ℕ, ∃ s > s₀, ¬directing_sentence₀ s ∧ up[str] (Λ s) = η := λ s₀,
begin
  have : ∃ s > s₀, up[str] (Λ s) = η, from str.infinite_substrategy_of_pi' Λ_thick pi s₀,
  rcases this with ⟨s, lt_s, rfl⟩,
  have : ¬directing_sentence₀ s, from (sigma_outcome_iff_of_even even).mp (str.Lambda_pi_outcome_of_thick Λ_thick pi s rfl),  
  refine ⟨s, lt_s, this, rfl⟩
end

lemma pi_substrategies_of_even
  {η : Tree 1} {t} {lt : η ⊂ᵢ (Λ[str] Λ) t} (pi : (out ⟨η, lt⟩).is_pi) (even : η.length.bodd = ff) :
  ¬ff ∈ ⟦η.length.div2⟧ᵪ^(chr I₀_inf) η.weight := λ A,
begin
  have : ∃ s₀, ⟦η.length.div2⟧ᵪ^(chr I₀_inf) [s₀] η.weight = ff, from rpartrec.univn_complete.mp A,
  rcases this with ⟨s₀, eq_ff⟩,
  have : ∃ t, ∀ a < s₀, a ∈ I₀ t ↔ a ∈ I₀_inf, from I₀_beq_exists s₀,
  rcases this with ⟨t₀, beq⟩,
  have : ∃ s₁, s₀ < (λ[str] (Λ s₁)).weight, from str.lambda_infinitely Λ_thick (by simp) _,
  rcases this with ⟨s₁, lt_weight⟩,
  let s₂ := max t₀ s₁,
  have : ∃ s > max t₀ s₁, ¬⟦(up[str] (Λ s)).length.div2⟧ᵪ^(I₀ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff ∧ 
    up[str] (Λ s) = η, from pi_substrategies_of_even_aux pi even _,
  rcases this with ⟨s, lt_s, ne_ff, rfl⟩,
  have le_s₀ : s₀ ≤ (λ[str] (Λ s)).weight,
    calc s₀ ≤ (λ[str] (Λ s₁)).weight : le_of_lt lt_weight
        ... ≤ (λ[str] (Λ s)).weight : str.weight_lambda_le_mono (Λ_thick.le_mono_iff.mpr (le_of_lt (max_lt_iff.mp lt_s).2)),
  have beq_s : ∀ a < s₀, (a ∈ I₀_inf ↔ a ∈ I₀ s),
  { intros a bound, split, 
    { intros mem, have : a ∈ I₀ t₀, from (beq a bound).mpr mem, exact I₀_mono (le_of_lt (max_lt_iff.mp lt_s).1) this },
    { intros mem, exact ⟨s, mem⟩ } },
  have : ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(I₀ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff,
    from rpartrec.univn_tot_mono_use (by { simp[←bool.coe_bool_iff], exact beq_s }) le_s₀ eq_ff,
  contradiction
end

lemma pi_substrategies_of_odd_aux
  {η : Tree 1} {t} {lt : η ⊂ᵢ (Λ[str] Λ) t} (pi : (out ⟨η, lt⟩).is_pi) (odd : η.length.bodd = tt) :
  ∀ s₀ : ℕ, ∃ s > s₀, ¬directing_sentence₁ s ∧ up[str] (Λ s) = η := λ s₀,
begin
  have : ∃ s > s₀, up[str] (Λ s) = η, from str.infinite_substrategy_of_pi' Λ_thick pi s₀,
  rcases this with ⟨s, lt_s, rfl⟩,
  have : ¬directing_sentence₁ s, from (sigma_outcome_iff_of_odd odd).mp (str.Lambda_pi_outcome_of_thick Λ_thick pi s rfl),  
  refine ⟨s, lt_s, this, rfl⟩
end

lemma pi_substrategies_of_odd
  {η : Tree 1} {t} {lt : η ⊂ᵢ (Λ[str] Λ) t} (pi : (out ⟨η, lt⟩).is_pi) (odd : η.length.bodd = tt) :
  ¬ff ∈ ⟦η.length.div2⟧ᵪ^(chr I₁_inf) η.weight := λ A,
begin
  have : ∃ s₀, ⟦η.length.div2⟧ᵪ^(chr I₁_inf) [s₀] η.weight = ff, from rpartrec.univn_complete.mp A,
  rcases this with ⟨s₀, eq_ff⟩,
  have : ∃ t, ∀ a < s₀, a ∈ I₁ t ↔ a ∈ I₁_inf, from I₁_beq_exists s₀,
  rcases this with ⟨t₀, beq⟩,
  have : ∃ s₁, s₀ < (λ[str] (Λ s₁)).weight, from str.lambda_infinitely Λ_thick (by simp) _,
  rcases this with ⟨s₁, lt_weight⟩,
  let s₂ := max t₀ s₁,
  have : ∃ s > max t₀ s₁, ¬⟦(up[str] (Λ s)).length.div2⟧ᵪ^(I₁ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff ∧ 
    up[str] (Λ s) = η, from pi_substrategies_of_odd_aux pi odd _,
  rcases this with ⟨s, lt_s, ne_ff, rfl⟩,
  have le_s₀ : s₀ ≤ (λ[str] (Λ s)).weight,
    calc s₀ ≤ (λ[str] (Λ s₁)).weight : le_of_lt lt_weight
        ... ≤ (λ[str] (Λ s)).weight : str.weight_lambda_le_mono (Λ_thick.le_mono_iff.mpr (le_of_lt (max_lt_iff.mp lt_s).2)),
  have beq_s : ∀ a < s₀, (a ∈ I₁_inf ↔ a ∈ I₁ s),
  { intros a bound, split, 
    { intros mem, have : a ∈ I₁ t₀, from (beq a bound).mpr mem, exact I₁_mono (le_of_lt (max_lt_iff.mp lt_s).1) this },
    { intros mem, exact ⟨s, mem⟩ } },
  have : ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(I₁ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff,
    from rpartrec.univn_tot_mono_use (by { simp[←bool.coe_bool_iff], exact beq_s }) le_s₀ eq_ff,
  contradiction
end


theorem not_I₁_le_I₀ : ¬I₁_inf ≤ₜ I₀_inf := λ hyp,
begin
  have : ∃ e, ⟦e⟧ᵪ^(chr I₀_inf) = chr I₁_inf, from rpartrec.exists_index.mp (classical_iff.mp hyp),
  rcases this with ⟨e, lmm_e⟩,
  have : ∃ η, η ⊂' Λ[str] Λ ∧ η.length = bit0 e, from (str.Lambda_infinite Λ_thick).lt_length_eq (bit0 e),
  rcases this with ⟨η, ⟨s₀, lt⟩, eq_len⟩,
  have even : η.length.bodd = ff, { simp[eq_len] },
  have eq_e : e = η.length.div2, { simp[eq_len] },  
  have : (out ⟨η, lt⟩).is_pi ∨ (out ⟨η, lt⟩).is_sigma, from pi_or_sigma (out ⟨η, lt⟩),
  rcases this with (pi | sigma),
  { have : η.weight ∉ I₁_inf, from nonmem_of_even pi even,
    have : ff ∈ ⟦e⟧ᵪ^(chr I₀_inf) η.weight, { simp[lmm_e], exact eq.symm ((chr_ff_iff _ _).mpr this) },
    have : ff ∉ ⟦e⟧ᵪ^(chr I₀_inf) η.weight, rw eq_e, from pi_substrategies_of_even pi even,
    contradiction },
  { have : η.weight ∈ I₁_inf ∧ ff ∈ ⟦e⟧ᵪ^(chr I₀_inf) η.weight, rw eq_e, from sigma_preservation_of_even sigma even,
    rcases this with ⟨mem, nonmem⟩,
    have : η.weight ∉ I₁_inf, { simp[lmm_e] at nonmem, exact (chr_ff_iff _ _).mp (eq.symm nonmem) },
    contradiction }
end

theorem not_I₀_le_I₁ : ¬I₀_inf ≤ₜ I₁_inf := λ hyp,
begin
  have : ∃ e, ⟦e⟧ᵪ^(chr I₁_inf) = chr I₀_inf, from rpartrec.exists_index.mp (classical_iff.mp hyp),
  rcases this with ⟨e, lmm_e⟩,
  have : ∃ η, η ⊂' Λ[str] Λ ∧ η.length = bit1 e, from (str.Lambda_infinite Λ_thick).lt_length_eq (bit1 e),
  rcases this with ⟨η, ⟨s₀, lt⟩, eq_len⟩,
  have odd : η.length.bodd = tt, { simp[eq_len] },
  have eq_e : e = η.length.div2, { simp[eq_len] },  
  have : (out ⟨η, lt⟩).is_pi ∨ (out ⟨η, lt⟩).is_sigma, from pi_or_sigma (out ⟨η, lt⟩),
  rcases this with (pi | sigma),
  { have : η.weight ∉ I₀_inf, from nonmem_of_odd pi odd,
    have : ff ∈ ⟦e⟧ᵪ^(chr I₁_inf) η.weight, { simp[lmm_e], exact eq.symm ((chr_ff_iff _ _).mpr this) },
    have : ff ∉ ⟦e⟧ᵪ^(chr I₁_inf) η.weight, rw eq_e, from pi_substrategies_of_odd pi odd,
    contradiction },
  { have : η.weight ∈ I₀_inf ∧ ff ∈ ⟦e⟧ᵪ^(chr I₁_inf) η.weight, rw eq_e, from sigma_preservation_of_odd sigma odd,
    rcases this with ⟨mem, nonmem⟩,
    have : η.weight ∉ I₀_inf, { simp[lmm_e] at nonmem, exact (chr_ff_iff _ _).mp (eq.symm nonmem) },
    contradiction }
end

end friedberg_muchnik
