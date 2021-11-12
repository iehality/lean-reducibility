import its reducibility its_computable

open encodable denumerable

attribute [simp] set.set_of_app_iff

namespace friedberg_muchnik
open rcomputable rcomputable₂
def str : strategy 1 := default _

def generator : ℕ → (Tree 0 × (list ℕ × list ℕ))
| 0       := ([], [], [])
| (s + 1) :=
    let μ  : Tree 0 := (generator s).1, 
        L₀ : list ℕ := (generator s).2.1,
        L₁ : list ℕ := (generator s).2.2,
        η  : Tree 1 := up[str] μ in
    match η.length.bodd with
    | ff := if ⟦η.length.div2⟧ᵪ^L₀.chr [(λ[str] μ).weight] η.weight = some ff then (∞ :: μ, L₀, η.weight :: L₁)
            else (𝟘 :: μ, L₀, L₁)
    | tt := if ⟦η.length.div2⟧ᵪ^L₁.chr [(λ[str] μ).weight] η.weight = some ff then (∞ :: μ, η.weight :: L₀, L₁)
            else (𝟘 :: μ, L₀, L₁)
    end

lemma computable.generator : computable generator :=
begin
  let F : ℕ → (Tree 0 × list ℕ × list ℕ) :=
  nat.elim ([], [], []) (λ s IH,
    let μ  : Tree 0 := IH.1, 
        L₀ : list ℕ := IH.2.1,
        L₁ : list ℕ := IH.2.2,
        η  : Tree 1 := up[str] μ in
    cond η.length.bodd
      (if ⟦η.length.div2⟧ᵪ^L₁.chr [(λ[str] μ).weight] η.weight = some ff then (∞ :: μ, η.weight :: L₀, L₁)
       else (𝟘 :: μ, L₀, L₁))
      (if ⟦η.length.div2⟧ᵪ^L₀.chr [(λ[str] μ).weight] η.weight = some ff then (∞ :: μ, L₀, η.weight :: L₁)
       else (𝟘 :: μ, L₀, L₁))),
  have : computable F,
  { refine rcomputable.computable_of_rcomp _,
    refine nat_elim' id ((const list.nil).pair ((const list.nil).pair (const list.nil))) _,
    refine rcomputable.cond
      (nat_bodd.comp $ list_length.comp (strategy.rcomputable.up.comp (fst.comp snd.to_unary₂))) _ _,
    { refine rcomputable.ite ((rcomputable₂.to_bool_eq _).comp _ (const (some ff)))
        ((list_cons.comp (const ∞) (fst.comp snd.to_unary₂)).pair
          ((list_cons.comp (strategy.rcomputable.Tree_weight.comp (strategy.rcomputable.up.comp (fst.comp snd.to_unary₂)))
            (fst.comp (snd.comp snd.to_unary₂))).pair
              (snd.comp (snd.comp snd.to_unary₂))))
        ((list_cons.comp (const 𝟘) (fst.comp snd.to_unary₂)).pair (snd.comp snd.to_unary₂)),
      refine rcomputable.univn_tot_s _ _
        (nat_div2.comp (list_length.comp (strategy.rcomputable.up.comp (fst.comp snd.to_unary₂))))
        (list_chr.comp (snd.comp (snd.comp (snd.comp snd.to_unary₁))) snd)
        (strategy.rcomputable.Tree_weight.comp (strategy.rcomputable.lambda.comp (fst.comp snd.to_unary₂)))
        (strategy.rcomputable.Tree_weight.comp (strategy.rcomputable.up.comp (fst.comp snd.to_unary₂))) },
    { refine rcomputable.ite ((rcomputable₂.to_bool_eq _).comp _ (const (some ff)))
        ((list_cons.comp (const ∞) (fst.comp snd.to_unary₂)).pair
          ((fst.comp (snd.comp snd.to_unary₂)).pair
            (list_cons.comp (strategy.rcomputable.Tree_weight.comp (strategy.rcomputable.up.comp (fst.comp snd.to_unary₂)))
              (snd.comp (snd.comp snd.to_unary₂)))))
        ((list_cons.comp (const 𝟘) (fst.comp snd.to_unary₂)).pair (snd.comp snd.to_unary₂)),
      refine rcomputable.univn_tot_s _ _
        (nat_div2.comp (list_length.comp (strategy.rcomputable.up.comp (fst.comp snd.to_unary₂))))
        (list_chr.comp (fst.comp (snd.comp (snd.comp snd.to_unary₁))) snd)
        (strategy.rcomputable.Tree_weight.comp (strategy.rcomputable.lambda.comp (fst.comp snd.to_unary₂)))
        (strategy.rcomputable.Tree_weight.comp (strategy.rcomputable.up.comp (fst.comp snd.to_unary₂))) } },
  exact this.of_eq (λ s, by {
    induction s with s IH; simp[F, generator],
    { simp[F] at IH, simp[IH], cases C : (list.length (up[str] (generator s).fst)).bodd; simp[C, generator] } })
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

def L₀ (s : ℕ) : list ℕ := (generator s).2.1

@[simp] lemma L₀_empty : L₀ 0 = [] := rfl

def L₁ (s : ℕ) : list ℕ := (generator s).2.2

@[simp] lemma L₁_empty : L₁ 0 = [] := rfl

def I₀ : set ℕ := {n | ∃ s, n ∈ L₀ s}

def I₁ : set ℕ := {n | ∃ s, n ∈ L₁ s}

lemma I₀_re : r.e. I₀ :=
begin
  suffices : 𝚺⁰1 I₀,
  { refine sigma_pred1_iff_re.mp this },
  let A : set ℕ := {n | n.unpair.1 ∈ (L₀ n.unpair.2)},
  simp[sigma_pred],
  refine ⟨A, _⟩,
  have : computable_pred A,
  { refine ⟨λ a, classical.dec _, _⟩,
    have : computable (λ a : ℕ, (L₀ a.unpair.2).chr a.unpair.1),
      from rcomputable.computable_of_rcomp (rcomputable.list_chr.comp
      (fst.comp $ snd.comp $ computable.generator.to_rcomp.comp (snd.comp nat_unpaired))
      (fst.comp nat_unpaired)),
    exact this.of_eq (λ a, by simp[A, list.chr]) },
  exact ⟨this, by { ext a, simp[I₀] }⟩
end

lemma I₁_re : r.e. I₁ :=
begin
  suffices : 𝚺⁰1 I₁,
  { refine sigma_pred1_iff_re.mp this },
  let A : set ℕ := {n | n.unpair.1 ∈ (L₁ n.unpair.2)},
  simp[sigma_pred],
  refine ⟨A, _⟩,
  have : computable_pred A,
  { refine ⟨λ a, classical.dec _, _⟩,
    have : computable (λ a : ℕ, (L₁ a.unpair.2).chr a.unpair.1),
      from rcomputable.computable_of_rcomp (rcomputable.list_chr.comp
      (snd.comp $ snd.comp $ computable.generator.to_rcomp.comp (snd.comp nat_unpaired))
      (fst.comp nat_unpaired)),
    exact this.of_eq (λ a, by simp[A, list.chr]) },
  exact ⟨this, by { ext a, simp[I₁] }⟩
end

@[reducible]
def directing_sentence₀ (s : ℕ) : Prop :=
⟦(up[str] (Λ s)).length.div2⟧ᵪ^(L₀ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff

@[reducible]
def directing_sentence₁ (s : ℕ) : Prop :=
⟦(up[str] (Λ s)).length.div2⟧ᵪ^(L₁ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff

lemma generator_eq_of_pi_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) :
  directing_sentence₀ s → generator (s + 1) = (∞ :: Λ s, L₀ s, (up[str] (Λ s)).weight :: L₁ s) := λ C,
by { simp[directing_sentence₀, L₀, L₁, Λ_app_eq] at C even, simp[generator, even, C, Λ_app_eq, L₀, L₁] }

lemma generator_eq_of_sigma_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) :
  ¬directing_sentence₀ s → generator (s + 1) = (𝟘 :: Λ s, L₀ s, L₁ s) := λ C,
by { simp[directing_sentence₀, L₀, L₁, Λ_app_eq] at C even, simp[generator, even, C, Λ_app_eq, L₀, L₁], intros h, contradiction }

lemma generator_eq_of_pi_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) :
  directing_sentence₁ s → generator (s + 1) = (∞ :: Λ s, (up[str] (Λ s)).weight :: L₀ s, L₁ s) := λ C,
by { simp[directing_sentence₁, L₀, L₁, Λ_app_eq] at C odd, simp[generator, odd, C, Λ_app_eq, L₀, L₁] }

lemma generator_eq_of_sigma_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) :
  ¬directing_sentence₁ s → generator (s + 1) = (𝟘 :: Λ s, L₀ s, L₁ s) := λ C,
by { simp[directing_sentence₁, L₀, L₁, Λ_app_eq] at C odd, simp[generator, odd, C, Λ_app_eq, L₀, L₁], intros h, contradiction }

lemma L₁_eq_of_pi_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) :
  directing_sentence₀ s → L₁ (s + 1) = (up[str] (Λ s)).weight :: L₁ s := λ C,
by simp[L₁, generator_eq_of_pi_of_even even C]

lemma L₁_eq_of_sigma_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) :
  ¬directing_sentence₀ s → L₁ (s + 1) = L₁ s := λ C,
by simp[L₁, generator_eq_of_sigma_of_even even C]

lemma L₀_eq_of_pi_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) :
  directing_sentence₁ s → L₀ (s + 1) = (up[str] (Λ s)).weight :: L₀ s := λ C,
by simp[L₀, generator_eq_of_pi_of_odd odd C]

lemma L₀_eq_of_sigma_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) :
  ¬directing_sentence₁ s → L₀ (s + 1) = L₀ s := λ C,
by simp[L₀, generator_eq_of_sigma_of_odd odd C]

@[simp] lemma L₁_eq_of_odd {s : ℕ} (odd : (up[str] (Λ s)).length.bodd = tt) : L₁ (s + 1) = L₁ s :=
by { by_cases C : directing_sentence₁ s,
     simp[L₁, generator_eq_of_pi_of_odd odd C], simp[L₁, generator_eq_of_sigma_of_odd odd C] }

@[simp] lemma L₀_eq_of_even {s : ℕ} (even : (up[str] (Λ s)).length.bodd = ff) : L₀ (s + 1) = L₀ s :=
by { by_cases C : directing_sentence₀ s,
     simp[L₀, generator_eq_of_pi_of_even even C], simp[L₀, generator_eq_of_sigma_of_even even C] }

lemma mem_I₁_of_pi_of_even {s} (even : (up[str] (Λ s)).length.bodd = ff) (pi : directing_sentence₀ s) :
  (up[str] (Λ s)).weight ∈ I₁ := ⟨s + 1, by simp[L₁_eq_of_pi_of_even even pi]⟩

lemma mem_I₀_of_pi_of_odd {s} (odd : (up[str] (Λ s)).length.bodd = tt) (pi : directing_sentence₁ s) :
  (up[str] (Λ s)).weight ∈ I₀ := ⟨s + 1, by simp[L₀_eq_of_pi_of_odd odd pi]⟩

lemma mem_L₁_iff (t a : ℕ) :
  a ∈ L₁ t ↔ ∃ s < t, (up[str] (Λ s)).length.bodd = ff ∧ a = (up[str] (Λ s)).weight ∧ directing_sentence₀ s :=
begin
  induction t with t IH,
  { simp },
  { rcases C : (up[str] (Λ t)).length.bodd with (C | C),
    { by_cases C₂ : directing_sentence₀ t,
      { simp[L₁_eq_of_pi_of_even C C₂, IH], split,
        { rintros (rfl | ⟨s, lt, s_even, rfl, pi⟩),
          { exact ⟨t, lt_add_one t, C, rfl, C₂⟩ }, { refine ⟨s, nat.lt.step lt, s_even, rfl, pi⟩ } },
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
          have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
          rcases this with (lt | rfl), { right, refine ⟨s, lt, s_even, rfl, pi⟩ }, { left, simp } } },
      { simp[L₁_eq_of_sigma_of_even C C₂, IH], split,
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩, refine ⟨s, nat.lt.step lt_s, s_even, rfl, pi⟩ },
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
          have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
          rcases this with (lt | rfl), { refine ⟨s, lt, s_even, rfl, pi⟩ }, { exfalso, contradiction } } } },
    { simp[L₁_eq_of_odd C, IH], split,
      { rintros ⟨s, lt_s, s_even, rfl, pi⟩, refine ⟨s, nat.lt.step lt_s, s_even, rfl, pi⟩ },
      { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
        have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
        rcases this with (lt | rfl),
        { refine ⟨s, lt, s_even, rfl, pi⟩ }, { exfalso, simp[C] at s_even, contradiction } } } }
end

lemma mem_L₀_iff (t a : ℕ) :
  a ∈ L₀ t ↔ ∃ s < t, (up[str] (Λ s)).length.bodd = tt ∧ a = (up[str] (Λ s)).weight ∧ directing_sentence₁ s :=
begin
  induction t with t IH,
  { simp },
  { rcases C : (up[str] (Λ t)).length.bodd with (C | C),
    { simp[L₀_eq_of_even C, IH], split,
      { rintros ⟨s, lt_s, s_even, rfl, pi⟩, refine ⟨s, nat.lt.step lt_s, s_even, rfl, pi⟩ },
      { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
        have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
        rcases this with (lt | rfl),
        { refine ⟨s, lt, s_even, rfl, pi⟩ }, { exfalso, simp[C] at s_even, contradiction } } },
    { by_cases C₂ : directing_sentence₁ t,
      { simp[L₀_eq_of_pi_of_odd C C₂, IH], split,
        { rintros (rfl | ⟨s, lt, s_even, rfl, pi⟩),
          { exact ⟨t, lt_add_one t, C, rfl, C₂⟩ }, { refine ⟨s, nat.lt.step lt, s_even, rfl, pi⟩ } },
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
          have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
          rcases this with (lt | rfl), { right, refine ⟨s, lt, s_even, rfl, pi⟩ }, { left, simp } } },
      { simp[L₀_eq_of_sigma_of_odd C C₂, IH], split,
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩, refine ⟨s, nat.lt.step lt_s, s_even, rfl, pi⟩ },
        { rintros ⟨s, lt_s, s_even, rfl, pi⟩,
          have : s < t ∨ s = t, from lt_or_eq_of_le (nat.lt_succ_iff.mp lt_s),
          rcases this with (lt | rfl), { refine ⟨s, lt, s_even, rfl, pi⟩ }, { exfalso, contradiction } } } } }
end

lemma L₁_mono {s₁ s₂ : ℕ} (le : s₁ ≤ s₂) : L₁ s₁ ⊆ L₁ s₂ := λ a mem,
by { simp [mem_L₁_iff] at mem ⊢, rcases mem with ⟨s, lt_s, h⟩, refine ⟨s, gt_of_ge_of_gt le lt_s, h⟩ }

lemma L₀_mono {s₁ s₂ : ℕ} (le : s₁ ≤ s₂) : L₀ s₁ ⊆ L₀ s₂ := λ a mem,
by { simp [mem_L₀_iff] at mem ⊢, rcases mem with ⟨s, lt_s, h⟩, refine ⟨s, gt_of_ge_of_gt le lt_s, h⟩ }

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
  a ∈ L₀ s₂ → a ∈ L₀ s₁ :=
begin
  simp only [mem_L₀_iff],
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
    up[str] (Λ s) = η ∧ ⟦η.length.div2⟧ᵪ^(chr I₀) [(λ[str] (Λ s)).weight] η.weight = ff :=
begin
  rcases str.Lambda_sigma_outcome_of_thick Λ Λ_thick lt sigma with ⟨s, rfl, eq_out, pi⟩,
  have pi : directing_sentence₀ s, from (pi_outcome_iff_of_even even).mp pi,
  have : ∀ a : ℕ, a < (λ[str] (Λ s)).weight → (L₀ s).chr a = chr I₀ a,
  { intros a bound, simp[←bool.coe_bool_iff],
    show a ∈ L₀ s ↔ I₀ a,
    refine ⟨λ h, ⟨s, h⟩, λ ⟨t, h⟩, sigma_preservation_of_pi_of_even
      even pi ⟨s₀, lt.suffix⟩ (le_max_left s t) (le_of_lt bound) (L₀_mono (le_max_right s t) h)⟩ },
  have : ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(L₀ s).chr [(λ[str] (Λ s)).weight] =
    ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(chr I₀) [(λ[str] (Λ s)).weight],
    from rpartrec.univn_tot_use this,
  refine ⟨s, pi, rfl, _⟩,  
  simp[←this], exact pi
end

lemma sigma_preservation_of_even
  {η : Tree 1} {s₀} {lt : η ⊂ᵢ (Λ[str] Λ) s₀} (sigma : (out ⟨η, lt⟩).is_sigma) (even : η.length.bodd = ff) :
  η.weight ∈ I₁ ∧ ff ∈ ⟦η.length.div2⟧ᵪ^(chr I₀) η.weight :=
by { rcases sigma_preservation_of_even_aux sigma even with ⟨s, pi, rfl, eqn⟩,
     simp[rpartrec.univn_complete],
     refine ⟨mem_I₁_of_pi_of_even even pi, (λ[str] (Λ s)).weight, eqn⟩}

lemma sigma_preservation_of_pi_of_odd
  {s₁ s₂} (odd : (up[str] (Λ s₁)).length.bodd = tt) (pi : directing_sentence₁ s₁) 
  (on_truepath : up[str] (Λ s₁) ⊆' Λ[str] Λ) (le : s₁ ≤ s₂) {a : ℕ} (bound : a ≤ (λ[str] (Λ s₁)).weight) :
  a ∈ L₁ s₂ → a ∈ L₁ s₁:=
begin
  simp only [mem_L₁_iff],
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
    up[str] (Λ s) = η ∧ ⟦η.length.div2⟧ᵪ^(chr I₁) [(λ[str] (Λ s)).weight] η.weight = ff :=
begin
  rcases str.Lambda_sigma_outcome_of_thick Λ Λ_thick lt sigma with ⟨s, rfl, eq_out, pi⟩,
  have pi : directing_sentence₁ s, from (pi_outcome_iff_of_odd odd).mp pi,
  have : ∀ a : ℕ, a < (λ[str] (Λ s)).weight → (L₁ s).chr a = chr I₁ a,
  { intros a bound, simp[←bool.coe_bool_iff],
    show a ∈ L₁ s ↔ I₁ a,
    refine ⟨λ h, ⟨s, h⟩, λ ⟨t, h⟩, sigma_preservation_of_pi_of_odd
      odd pi ⟨s₀, lt.suffix⟩ (le_max_left s t) (le_of_lt bound) (L₁_mono (le_max_right s t) h)⟩ },
  have : ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(L₁ s).chr [(λ[str] (Λ s)).weight] =
    ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(chr I₁) [(λ[str] (Λ s)).weight],
    from rpartrec.univn_tot_use this,
  refine ⟨s, pi, rfl, _⟩,  
  simp[←this], exact pi
end

lemma sigma_preservation_of_odd
  {η : Tree 1} {s₀} {lt : η ⊂ᵢ (Λ[str] Λ) s₀} (sigma : (out ⟨η, lt⟩).is_sigma) (odd : η.length.bodd = tt) :
  η.weight ∈ I₀ ∧ ff ∈ ⟦η.length.div2⟧ᵪ^(chr I₁) η.weight :=
by { rcases sigma_preservation_of_odd_aux sigma odd with ⟨s, pi, rfl, eqn⟩,
     simp[rpartrec.univn_complete],
     refine ⟨mem_I₀_of_pi_of_odd odd pi, (λ[str] (Λ s)).weight, eqn⟩ }

lemma nonmem_of_even
  {η : Tree 1} {t} {lt : η ⊂ᵢ (Λ[str] Λ) t} (pi : (out ⟨η, lt⟩).is_pi) (even : η.length.bodd = ff) :
  η.weight ∉ I₁ := λ mem,
begin
  rcases mem with ⟨s₀, mem⟩,
  rcases (mem_L₁_iff s₀ η.weight).mp mem with ⟨s, lt_s, _, eq_weight, pi⟩,
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
  η.weight ∉ I₀ := λ mem,
begin
  rcases mem with ⟨s₀, mem⟩,
  rcases (mem_L₀_iff s₀ η.weight).mp mem with ⟨s, lt_s, _, eq_weight, pi⟩,
  have : η = up[str] (Λ s),
  { rcases str.le_Lambda_of_thick' Λ_thick ⟨t, lt.suffix⟩ with ⟨s₀, rfl, _⟩, simp at*,
    rcases str.eq_lambda_of_le_lambda' (str.up_le_lambda (Λ s)) with ⟨μ₀, le_μ₀, eq_up⟩,
    rcases Λ_thick.ssubset.mp ⟨s, le_μ₀⟩ with ⟨s', rfl⟩,
    simp[eq_up] at eq_weight ⊢, exact str.weight_lambda_inj_of_thick Λ_thick eq_weight },
  rcases this with rfl,
  have : ¬directing_sentence₁ s, from (sigma_outcome_iff_of_odd odd).mp (str.Lambda_pi_outcome_of_thick Λ_thick pi s rfl),
  contradiction
end

lemma L₀_beq_exists(b : ℕ) :
  ∃ s, ∀ a < b, a ∈ L₀ s ↔ a ∈ I₀ :=
begin
  induction b with b IH,
  { simp },
  { rcases IH with ⟨s₀, beq⟩,
    by_cases C : b ∈ I₀,
    { rcases C with ⟨s_b, mem⟩,
      refine ⟨max s₀ s_b, λ a bound, _⟩,
      split, { intros mem, refine ⟨_, mem⟩ },
      intros mem,
      have : a < b ∨ a = b, from lt_or_eq_of_le (nat.lt_succ_iff.mp bound),
      rcases this with (lt | rfl),
      { have : a ∈ L₀ s₀, from (beq a lt).mpr mem, exact L₀_mono (le_max_left s₀ s_b) this },
      { exact L₀_mono (le_max_right s₀ s_b) mem } },
    { refine ⟨s₀, λ a bound, _⟩,
      have : a < b ∨ a = b, from lt_or_eq_of_le (nat.lt_succ_iff.mp bound),
      rcases this with (lt | rfl),
      { exact beq a lt },
      { simp[C], intros mem, have : a ∈ I₀, from ⟨s₀, mem⟩, contradiction } } }
end

lemma L₁_beq_exists(b : ℕ) :
  ∃ s, ∀ a < b, a ∈ L₁ s ↔ a ∈ I₁ :=
begin
  induction b with b IH,
  { simp },
  { rcases IH with ⟨s₀, beq⟩,
    by_cases C : b ∈ I₁,
    { rcases C with ⟨s_b, mem⟩,
      refine ⟨max s₀ s_b, λ a bound, _⟩,
      split, { intros mem, refine ⟨_, mem⟩ },
      intros mem,
      have : a < b ∨ a = b, from lt_or_eq_of_le (nat.lt_succ_iff.mp bound),
      rcases this with (lt | rfl),
      { have : a ∈ L₁ s₀, from (beq a lt).mpr mem, exact L₁_mono (le_max_left s₀ s_b) this },
      { exact L₁_mono (le_max_right s₀ s_b) mem } },
    { refine ⟨s₀, λ a bound, _⟩,
      have : a < b ∨ a = b, from lt_or_eq_of_le (nat.lt_succ_iff.mp bound),
      rcases this with (lt | rfl),
      { exact beq a lt },
      { simp[C], intros mem, have : a ∈ I₁, from ⟨s₀, mem⟩, contradiction } } }
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
  ¬ff ∈ ⟦η.length.div2⟧ᵪ^(chr I₀) η.weight := λ A,
begin
  have : ∃ s₀, ⟦η.length.div2⟧ᵪ^(chr I₀) [s₀] η.weight = ff, from rpartrec.univn_complete.mp A,
  rcases this with ⟨s₀, eq_ff⟩,
  have : ∃ t, ∀ a < s₀, a ∈ L₀ t ↔ a ∈ I₀, from L₀_beq_exists s₀,
  rcases this with ⟨t₀, beq⟩,
  have : ∃ s₁, s₀ < (λ[str] (Λ s₁)).weight, from str.lambda_infinitely Λ_thick (by simp) _,
  rcases this with ⟨s₁, lt_weight⟩,
  let s₂ := max t₀ s₁,
  have : ∃ s > max t₀ s₁, ¬⟦(up[str] (Λ s)).length.div2⟧ᵪ^(L₀ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff ∧ 
    up[str] (Λ s) = η, from pi_substrategies_of_even_aux pi even _,
  rcases this with ⟨s, lt_s, ne_ff, rfl⟩,
  have le_s₀ : s₀ ≤ (λ[str] (Λ s)).weight,
    calc s₀ ≤ (λ[str] (Λ s₁)).weight : le_of_lt lt_weight
        ... ≤ (λ[str] (Λ s)).weight : str.weight_lambda_le_mono (Λ_thick.le_mono_iff.mpr (le_of_lt (max_lt_iff.mp lt_s).2)),
  have beq_s : ∀ a < s₀, (a ∈ I₀ ↔ a ∈ L₀ s),
  { intros a bound, split, 
    { intros mem, have : a ∈ L₀ t₀, from (beq a bound).mpr mem, exact L₀_mono (le_of_lt (max_lt_iff.mp lt_s).1) this },
    { intros mem, exact ⟨s, mem⟩ } },
  have : ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(L₀ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff,
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
  ¬ff ∈ ⟦η.length.div2⟧ᵪ^(chr I₁) η.weight := λ A,
begin
  have : ∃ s₀, ⟦η.length.div2⟧ᵪ^(chr I₁) [s₀] η.weight = ff, from rpartrec.univn_complete.mp A,
  rcases this with ⟨s₀, eq_ff⟩,
  have : ∃ t, ∀ a < s₀, a ∈ L₁ t ↔ a ∈ I₁, from L₁_beq_exists s₀,
  rcases this with ⟨t₀, beq⟩,
  have : ∃ s₁, s₀ < (λ[str] (Λ s₁)).weight, from str.lambda_infinitely Λ_thick (by simp) _,
  rcases this with ⟨s₁, lt_weight⟩,
  let s₂ := max t₀ s₁,
  have : ∃ s > max t₀ s₁, ¬⟦(up[str] (Λ s)).length.div2⟧ᵪ^(L₁ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff ∧ 
    up[str] (Λ s) = η, from pi_substrategies_of_odd_aux pi odd _,
  rcases this with ⟨s, lt_s, ne_ff, rfl⟩,
  have le_s₀ : s₀ ≤ (λ[str] (Λ s)).weight,
    calc s₀ ≤ (λ[str] (Λ s₁)).weight : le_of_lt lt_weight
        ... ≤ (λ[str] (Λ s)).weight : str.weight_lambda_le_mono (Λ_thick.le_mono_iff.mpr (le_of_lt (max_lt_iff.mp lt_s).2)),
  have beq_s : ∀ a < s₀, (a ∈ I₁ ↔ a ∈ L₁ s),
  { intros a bound, split, 
    { intros mem, have : a ∈ L₁ t₀, from (beq a bound).mpr mem, exact L₁_mono (le_of_lt (max_lt_iff.mp lt_s).1) this },
    { intros mem, exact ⟨s, mem⟩ } },
  have : ⟦(up[str] (Λ s)).length.div2⟧ᵪ^(L₁ s).chr [(λ[str] (Λ s)).weight] (up[str] (Λ s)).weight = ff,
    from rpartrec.univn_tot_mono_use (by { simp[←bool.coe_bool_iff], exact beq_s }) le_s₀ eq_ff,
  contradiction
end


theorem not_I₁_le_I₀ : ¬I₁ ≤ₜ I₀ := λ hyp,
begin
  have : ∃ e, ⟦e⟧ᵪ^(chr I₀) = chr I₁, from rpartrec.exists_index.mp (classical_iff.mp hyp),
  rcases this with ⟨e, lmm_e⟩,
  have : ∃ η, η ⊂' Λ[str] Λ ∧ η.length = bit0 e, from (str.Lambda_infinite Λ_thick).lt_length_eq (bit0 e),
  rcases this with ⟨η, ⟨s₀, lt⟩, eq_len⟩,
  have even : η.length.bodd = ff, { simp[eq_len] },
  have eq_e : e = η.length.div2, { simp[eq_len] },  
  have : (out ⟨η, lt⟩).is_pi ∨ (out ⟨η, lt⟩).is_sigma, from pi_or_sigma (out ⟨η, lt⟩),
  rcases this with (pi | sigma),
  { have : η.weight ∉ I₁, from nonmem_of_even pi even,
    have : ff ∈ ⟦e⟧ᵪ^(chr I₀) η.weight, { simp[lmm_e], exact eq.symm ((chr_ff_iff _ _).mpr this) },
    have : ff ∉ ⟦e⟧ᵪ^(chr I₀) η.weight, rw eq_e, from pi_substrategies_of_even pi even,
    contradiction },
  { have : η.weight ∈ I₁ ∧ ff ∈ ⟦e⟧ᵪ^(chr I₀) η.weight, rw eq_e, from sigma_preservation_of_even sigma even,
    rcases this with ⟨mem, nonmem⟩,
    have : η.weight ∉ I₁, { simp[lmm_e] at nonmem, exact (chr_ff_iff _ _).mp (eq.symm nonmem) },
    contradiction }
end

theorem not_I₀_le_I₁ : ¬I₀ ≤ₜ I₁ := λ hyp,
begin
  have : ∃ e, ⟦e⟧ᵪ^(chr I₁) = chr I₀, from rpartrec.exists_index.mp (classical_iff.mp hyp),
  rcases this with ⟨e, lmm_e⟩,
  have : ∃ η, η ⊂' Λ[str] Λ ∧ η.length = bit1 e, from (str.Lambda_infinite Λ_thick).lt_length_eq (bit1 e),
  rcases this with ⟨η, ⟨s₀, lt⟩, eq_len⟩,
  have odd : η.length.bodd = tt, { simp[eq_len] },
  have eq_e : e = η.length.div2, { simp[eq_len] },  
  have : (out ⟨η, lt⟩).is_pi ∨ (out ⟨η, lt⟩).is_sigma, from pi_or_sigma (out ⟨η, lt⟩),
  rcases this with (pi | sigma),
  { have : η.weight ∉ I₀, from nonmem_of_odd pi odd,
    have : ff ∈ ⟦e⟧ᵪ^(chr I₁) η.weight, { simp[lmm_e], exact eq.symm ((chr_ff_iff _ _).mpr this) },
    have : ff ∉ ⟦e⟧ᵪ^(chr I₁) η.weight, rw eq_e, from pi_substrategies_of_odd pi odd,
    contradiction },
  { have : η.weight ∈ I₀ ∧ ff ∈ ⟦e⟧ᵪ^(chr I₁) η.weight, rw eq_e, from sigma_preservation_of_odd sigma odd,
    rcases this with ⟨mem, nonmem⟩,
    have : η.weight ∉ I₀, { simp[lmm_e] at nonmem, exact (chr_ff_iff _ _).mp (eq.symm nonmem) },
    contradiction }
end

theorem incomparable_re_sets : ∃ I₀ I₁ : set ℕ, r.e. I₀ ∧ r.e. I₁ ∧ ¬I₁ ≤ₜ I₀ ∧ ¬I₀ ≤ₜ I₁ :=
⟨I₀, I₁, I₀_re, I₁_re, not_I₁_le_I₀, not_I₀_le_I₁⟩

end friedberg_muchnik
