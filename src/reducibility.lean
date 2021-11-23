import coding function
import computability.reduce
open encodable denumerable part

universes u v

local attribute [simp] set.set_of_app_iff

lemma bool.to_bool_ext (p : Prop) (D0 D1 : decidable p) :
  @to_bool p D0 = @to_bool p D1 := 
by { cases (@decidable.em p D0) with h,
     simp[to_bool_tt h], exact h, simp[to_bool_ff h], exact h, }

lemma bool.to_bool_ext_iff {p q : Prop} (r : p ↔ q) (D0 : decidable p) (D1 : decidable q) :
  @to_bool _ D0 = @to_bool _ D1 := 
by { cases (@decidable.em p D0) with h, simp[to_bool_tt h],
     exact r.mp h, simp[to_bool_ff h], exact (not_congr r).mp h, }

lemma bool.to_bool_ext_bnot (p : Prop) (D0 : decidable p) (D1 : decidable ¬p) :
  @to_bool _ D1 = !@to_bool _ D0 := 
by { cases (@decidable.em p D0) with h,
     simp[to_bool_tt h], exact h, simp[to_bool_ff h], exact h, }

lemma encode_to_bool_eq {α} {A : set α} (D0 D1 : decidable_pred A) :
  (λ n, (@to_bool (A n) (D0 n))) = (λ n, (@to_bool (A n) (D1 n))) := funext (λ x, by rw bool.to_bool_ext)

lemma decidable_pred.compl {α} {A : set α} :
  decidable_pred A → decidable_pred Aᶜ := λ h x, @not.decidable _ (h x)

noncomputable def chr {α} (p : set α)  : α → bool := λ x : α,
decidable.cases_on (classical.dec (p x)) (λ h₁, bool.ff) (λ h₂, bool.tt)

@[simp] theorem chr_tt_iff {α} (A : set α) (x : α) : chr A x = tt ↔ A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

@[simp] theorem chr_tt_iff_r {α} (A : set α) (x : α) : tt = chr A x ↔ A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

@[simp] theorem chr_ff_iff {α} (A : set α) (x : α) : chr A x = ff ↔ ¬A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

@[simp] theorem chr_ff_iff_r {α} (A : set α) (x : α) : ff = chr A x ↔ ¬A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

theorem chr_iff {α} (A : set α) (x : α) (b : bool) : chr A x = b ↔ (A x ↔ b = tt) :=
by cases b; simp

@[simp] theorem chr_app_iff {α} (A : set α) (x : α) : chr A x ↔ A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

theorem chr_eq_to_bool {α} (A : set α) (x : α) [decidable (A x)] : chr A x = to_bool (A x) :=
by simp[chr_iff]

theorem to_bool_chr_eq {α} (A : set α) (x : α) (D : decidable (A x)) :
  to_bool (A x) = chr A x :=
by { cases (@decidable.em (A x) D) with h,
     simp[to_bool_tt h, (chr_tt_iff _ _).2 h],
     simp[to_bool_ff h, (chr_ff_iff _ _).2 h] }

theorem chr_ext {α β} {A : set α} {B : set β} {x y} : chr A x = chr B y ↔ (A x ↔ B y) :=
begin
    split,
  { assume h,
    cases e : chr A x, 
    have ax := (chr_ff_iff _ _).mp e,
    have bx := (chr_ff_iff B y).mp (by simp[←h, e]), simp[ax,bx],
    have ax := (chr_tt_iff _ _).mp e,
    have bx := (chr_tt_iff B y).mp (by simp[←h, e]), simp[ax,bx] },
  { assume h, 
    cases e : chr B y,
    have bx := (chr_ff_iff _ _).mp e,
    exact (chr_ff_iff A x).mpr (by simp [h, bx]),
    have bx := (chr_tt_iff _ _).mp e,
    exact (chr_tt_iff A x).mpr (by simp [h, bx]) }
end

@[simp] lemma chr_coe_bool {α} (f : α → bool) : chr {x | f x = tt} = f :=
by funext a; cases C : f a; simp; exact C

def rre_pred {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  (p : set α) (f : β →. σ) : Prop :=
(λ a, part.assert (p a) (λ _, part.some ())) partrec_in f

infix ` re_in `:80 := rre_pred
prefix `r.e. `:80 := re_pred

def rre_pred_tot {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  (p : set α) (f : β → σ) : Prop := p re_in ↑ᵣf

infix ` re_in! `:80 := rre_pred_tot

theorem rre_pred.re {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  {A : set α} {f : β →. σ} (hA : A re_in f) (hf : partrec f) : r.e. A :=
hA.le_part_part hf

theorem rre_pred.re0 {α} [primcodable α]
  {A : set α} (hA : A re_in! chr (∅ : set ℕ)) : r.e. A :=
by { have : partrec ↑ᵣ(chr ∅ : ℕ → bool),
     { exact ((computable.const ff).of_eq $ λ x,
       by { symmetry, simp [chr_ff_iff], exact not_false }) },
     exact hA.re this }

theorem rre_in_0_iff_re {α} [primcodable α] {A : set α} :
  A re_in! chr (∅ : set ℕ) ↔ r.e. A :=
⟨rre_pred.re0, partrec.to_rpart⟩

def rcomputable_pred {α β γ} [primcodable α] [primcodable β] [primcodable γ] (A : set α) (o : β →. γ) : Prop := 
∃ [D0 : decidable_pred A],
by exactI (λ x, to_bool (A x)) computable_in o

def t_reducible {α β} [primcodable α] [primcodable β] (A : set α) (B : set β) : Prop := 
∃ [D0 : decidable_pred A] [D1 : decidable_pred B],
by exactI (λ x, to_bool (A x)) computable_in! (λ x, to_bool (B x)) 

infix ` ≤ₜ `:50 := t_reducible

@[reducible] def t_irreducible {α β} [primcodable α] [primcodable β] (A : set α) (B : set β) : Prop := ¬A ≤ₜ B

infix ` ≰ₜ ` :50 := t_irreducible

@[reducible] def t_reducible_lt {α β} [primcodable α] [primcodable β] (A : set α) (B : set β) : Prop :=
A ≤ₜ B ∧ ¬B ≤ₜ A

infix ` <ₜ `:50 := t_reducible_lt

def t_reducible_equiv {α β} [primcodable α] [primcodable β] (A : set α) (B : set β) : Prop :=
A ≤ₜ B ∧ B ≤ₜ A

infix ` ≡ₜ `:50 := t_reducible_equiv

def productive (A : set ℕ) : Prop :=
∃ φ : ℕ →. ℕ, partrec φ ∧ ∀ i : ℕ, W⟦i⟧ₙ⁰ ⊆ A → ∃ z, z ∈ φ i ∧ z ∈ A ∧ z ∉ W⟦i⟧ₙ⁰

def creative (A : set ℕ) : Prop := r.e. A ∧ productive Aᶜ

def immune (A : set ℕ) : Prop := infinite A ∧ ∀ e, infinite W⟦e⟧ₙ⁰ → W⟦e⟧ₙ⁰ ∩ Aᶜ ≠ ∅

def simple (A : set ℕ) : Prop := r.e. A ∧ immune Aᶜ 

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem classical_iff {A : set α} {B : set β} :
  A ≤ₜ B ↔ chr A computable_in! (chr B) :=
by simp[t_reducible, to_bool_chr_eq]; exact
  ⟨λ ⟨_, _, h⟩, h, λ h, ⟨classical.dec_pred _, classical.dec_pred _, h⟩⟩

theorem t_reducible.of_eq {A B : set α} {C : set β} (hA : A ≤ₜ C) (H : ∀ n, A n ↔ B n) : B ≤ₜ C :=
(set.ext H : A = B) ▸ hA

@[refl] theorem t_reducible.refl (A : set α) [D : decidable_pred A] : A ≤ₜ A := ⟨D, D, nat.rpartrec.refl⟩

@[trans] theorem t_reducible.trans {A : set α} {B : set β} {C : set γ} :
  A ≤ₜ B → B ≤ₜ C → A ≤ₜ C :=
λ ⟨Da, Db, hab⟩ ⟨Db0, Dc, hbc⟩,
⟨Da, Dc, by simp only [encode_to_bool_eq Db Db0] at hab; exact nat.rpartrec.trans hab hbc⟩

@[refl] theorem t_reducible_equiv.refl
  (A : set α) [D : decidable_pred A] :
  A ≡ₜ A :=
⟨t_reducible.refl A, t_reducible.refl A⟩

@[symm] theorem t_reducible_equiv.symm
  {A : set α} {B : set β} :
  A ≡ₜ B → B ≡ₜ A :=
and.swap

@[trans] theorem t_reducible_equiv.trans 
  {A : set α} {B : set β} {C : set γ} :
  A ≡ₜ B → B ≡ₜ C → A ≡ₜ C :=
λ ⟨ab, ba⟩ ⟨bc, cb⟩, ⟨t_reducible.trans ab bc, t_reducible.trans cb ba⟩

theorem many_one_reducible.to_turing {A : set α} {B : set β} [DA : decidable_pred A] [DB : decidable_pred B] :
  A ≤₀ B → A ≤ₜ B := λ h,
⟨DA, DB, by { rcases h with ⟨f, cf, hf⟩,
 exact ((rcomputable.refl.comp (cf.to_rcomp)).of_eq $ λ n, by simp [hf]) }⟩

theorem one_one_reducible.to_turing {A : set α} {B : set β} [DA : decidable_pred A] [DB : decidable_pred B] :
  A ≤₁ B → A ≤ₜ B := λ h, h.to_many_one.to_turing

theorem reducible_compl (A : set α) [D : decidable_pred A] : Aᶜ ≤ₜ A :=
have Dc : decidable_pred Aᶜ, from D.compl,
have e0 : ∀ x, @to_bool (Aᶜ x) (Dc x) = !to_bool (A x), from λ x, bool.to_bool_ext_bnot _ _ _,
have cb : computable bnot, from (primrec.dom_bool _).to_comp,
⟨Dc, D, (cb.to_rpart.comp rcomputable.refl).of_eq $ λ x, by simp[e0]⟩

theorem equiv_compl (A : set α) [D : decidable_pred A] : Aᶜ ≡ₜ A :=
have cc : Aᶜᶜ = A, from compl_compl A,
⟨reducible_compl A, by { 
  suffices : Aᶜᶜ ≤ₜ Aᶜ, rw cc at this, exact this, exact @reducible_compl _ _ Aᶜ D.compl, }⟩ 

theorem computable_le {A : set α} (B : set β) [D : decidable_pred B] :
  computable_pred A → A ≤ₜ B :=
λ ⟨D0, hA⟩, ⟨D0, D, nat.rpartrec.of_partrec _ hA⟩

theorem le_computable_computable {A : set α} {B : set β} :
  B ≤ₜ A → computable_pred A → computable_pred B := λ ⟨Db, Da, h⟩ ⟨Da0, hA⟩,
⟨Db, by { simp only [computable, partrec, encode_to_bool_eq Da0 Da] at hA,
          exact rpartrec.le_part_part h hA}⟩

theorem computable_equiv {A : set α} {B : set β} :
  computable_pred A → computable_pred B → A ≡ₜ B :=
λ ⟨Da, ca⟩ ⟨Db, cb⟩, ⟨@computable_le _ _ _ _ A B Db ⟨Da, ca⟩, @computable_le _ _ _ _ B A Da ⟨Db, cb⟩⟩

theorem computable_0 : computable_pred (∅ : set α) := 
⟨λ x, decidable.false, ((computable.const ff).of_eq $ λ x, rfl)⟩

theorem re_pred_0 : r.e. (∅ : set α) := 
partrec.none.of_eq (λ x, by {rw[show (∅ : set α) x = false, by refl], symmetry, simp[part.eq_none_iff] })

theorem degree0 (A : set α) :
  computable_pred A ↔ A ≡ₜ (∅ : set β) := 
⟨λ ⟨D, h⟩, ⟨computable_le _ ⟨D, h⟩, @computable_le _ _ _ _ _ _ D computable_0⟩,
 λ ⟨h, _⟩, le_computable_computable h computable_0⟩

 theorem computable_pred_iff_le {A : set α} :
  computable_pred A ↔ A ≤ₜ (∅ : set ℕ) := 
⟨λ ⟨D, h⟩, computable_le _ ⟨D, h⟩,
 λ h, le_computable_computable h computable_0⟩

theorem degree0' (A : set α) : computable_pred A ↔ A ≡ₜ (∅ : set ℕ) := degree0 A

def Join (A : ℕ → set ℕ) : set ℕ := {x | x.unpair.1 ∈ A x.unpair.2}

prefix `⨁`:90 := Join

theorem Join_one_one_reducible (A : ℕ → set ℕ) [D : ∀ n, decidable_pred (A n)] (n) : A n ≤₁ ⨁A :=
begin
  let f := (λ m : ℕ, m.mkpair n),
  have cf : computable f := (primrec₂.mkpair.comp primrec.id (primrec.const n)).to_comp,
  refine ⟨f, cf, _, _⟩,
  { intros x y h, simp[f] at h, have : x = (x.mkpair n).unpair.1, simp,
      rw this, rw h, simp },
  { intros x, simp [Join], refl }
end

theorem Join_le (A : ℕ → set ℕ) [DA : ∀ n, decidable_pred (A n)] 
  (B : set ℕ) [DB : decidable_pred B] (hA : (λ x y, to_bool (A x y)) computable₂_in! λ x, to_bool (B x)) : ⨁A ≤ₜ B :=
⟨λ a, DA (nat.unpair a).2 (nat.unpair a).1, DB, by { simp[Join],
  refine hA.comp (rcomputable.snd.comp rcomputable.nat_unpaired) (rcomputable.fst.comp rcomputable.nat_unpaired) }⟩

def Join₂ (A B : set ℕ) := ⨁(λ n, if n = 0 then A else if n = 1 then B else {})

theorem le_Join₂_left (A B : set ℕ) [DA : decidable_pred A] [DB : decidable_pred B] : A ≤₁ Join₂ A B :=
@Join_one_one_reducible (λ n, if n = 0 then A else if n = 1 then B else {})
  (λ n a, by { cases n; simp, { exact DA a }, cases n; simp, { exact DB a }, { exact decidable.false } }) 0

theorem le_Join₂_right (A B : set ℕ) [DA : decidable_pred A] [DB : decidable_pred B] : B ≤₁ Join₂ A B :=
@Join_one_one_reducible (λ n, if n = 0 then A else if n = 1 then B else {})
  (λ n a, by { cases n; simp, { exact DA a }, cases n; simp, { exact DB a }, { exact decidable.false } }) 1

theorem Join₂_le  (A B C : set ℕ) [DA : decidable_pred A] [DB : decidable_pred B] [DC : decidable_pred C]
  (hA : A ≤ₜ C) (hB : B ≤ₜ C) : Join₂ A B ≤ₜ C :=
@Join_le (λ n, if n = 0 then A else if n = 1 then B else {})
  (λ n a, by { cases n; simp, { exact DA a }, cases n; simp, { exact DB a }, { exact decidable.false } })
  C DC (by { rcases hA with ⟨_, _, cA⟩, rcases hB with ⟨_, _, cB⟩,
    simp,
    suffices : (λ (x y : ℕ), if x = 0 then (to_bool (A y)) else if x = 1 then to_bool (B y) else ff) computable₂_in! λ x, to_bool (C x),
    exact this.of_eq (λ n m, by { cases n; simp, cases n; simp[has_emptyc.emptyc] }),
    refine rcomputable.ite (rcomputable.to_bool_eq ℕ rcomputable.fst (rcomputable.const 0)) _ _,
    exact cast (by { congr, funext x, 
      exact (@bool.to_bool_eq (A x.snd) (A x.snd) (hA_w x.snd) (DA x.snd)).mpr (by refl), 
      funext x, simp }) (cA.comp rcomputable.snd),
    refine rcomputable.ite (rcomputable.to_bool_eq ℕ rcomputable.fst (rcomputable.const 1)) _ (rcomputable.const ff),
    exact cast (by { congr, funext x, 
      exact (@bool.to_bool_eq (B x.snd) (B x.snd) (hB_w x.snd) (DB x.snd)).mpr (by refl), 
      funext x, simp }) (cB.comp rcomputable.snd) })

section classical
local attribute [instance, priority 0] classical.prop_decidable
open rpartrec

theorem cond_if_eq {α β} (p : set α) (x) (a b : β) :
  cond (chr p x) a b = if p x then a else b :=
by {by_cases h : p x; simp [h], simp [(chr_tt_iff p x).mpr h], simp [(chr_ff_iff p x).mpr h] }

def Jump (A : set ℕ) : set ℕ := {x | (⟦x.unpair.1⟧ₙ^(chr A) x.unpair.2).dom}

notation A`′`:1200 := Jump A

@[simp] def Jump_itr : ℕ → set ℕ → set ℕ
| 0     A := A
| (n+1) A := (Jump_itr n A)′

theorem lt_Jump (A : set ℕ) : A <ₜ A′ := 
⟨classical_iff.mpr
  begin
    show chr A computable_in! chr A′,
    have : ∃ e, ∀ x, (⟦e⟧ₙ^(chr A) x).dom ↔ A x,
    { have : ∃ e, ⟦e⟧ₙ^(chr A) = λ a, cond (chr A a) (some 0) none :=
        exists_index.mp (bool_to_part (chr A)),
      rcases this with ⟨e, he⟩,
      refine ⟨e, λ x, _⟩,
      show (⟦e⟧ₙ^(chr A) x).dom ↔ A x,
      simp [he],
      cases e : chr A x,
      simp[(chr_ff_iff _ _).1 e], rintros ⟨f, _⟩, 
      simp[(chr_tt_iff _ _).1 e] },
    rcases this with ⟨e, he⟩,
    let f := λ x, chr A′ (e.mkpair x),
    have lmm_f : f computable_in! chr A′ :=
        (rcomputable.refl.comp (primrec₂.mkpair.comp (primrec.const e) primrec.id).to_rcomp),
    have : f = chr A,
    { funext x, simp[f, Jump, chr_ext, set.set_of_app_iff, he], },
    simp [←this], exact lmm_f,
  end,
  λ h : A′ ≤ₜ A,
  begin
    have l0 : chr A′ computable_in! chr A := classical_iff.mp h,
    have : ∃ e, ∀ x : ℕ, (⟦e⟧ₙ^(chr A) x).dom ↔ (x.mkpair x) ∉ A′,
    { let f : ℕ →. ℕ := (λ a, cond (chr A′ (a.mkpair a)) none (some 0)),
      have : f partrec_in! chr A := 
        ((rpartrec.cond (rpartrec.refl_in $ (chr A′ : ℕ →. bool))
        partrec.none.to_rpart (rcomputable.const 0)).comp
          (primrec₂.mkpair.comp primrec.id primrec.id).to_rcomp).trans l0,
      have : ∃ e, ⟦e⟧ₙ^(chr A) = f := exists_index.mp this,
      rcases this with ⟨e, he⟩,
      refine ⟨e, λ x, _⟩,
      simp[he, set.mem_def, f],
      cases e : chr A′ (x.mkpair x),
      simp[(chr_ff_iff _ _).1 e],
      simp[(chr_tt_iff _ _).1 e], rintros ⟨_, _⟩ },
    rcases this with ⟨e, he⟩,
    have : (e.mkpair e) ∉ A′ ↔ (e.mkpair e) ∈ A′,
    calc
      (e.mkpair e) ∉ A′ ↔ ¬(⟦e⟧ₙ^(chr A) e).dom : by simp[Jump]
                    ... ↔ (e.mkpair e) ∈ A′     : by simp[he],
    show false, from (not_iff_self _).mp this
  end⟩

theorem le_le_Jump {A B : set ℕ} : A ≤ₜ B → A′ ≤₁ B′ := λ h,
begin
  have h' := classical_iff.mp h,
  let f := (λ x : ℕ, ⟦x.unpair.1⟧ₙ^(chr A) x.unpair.2),
  have : ∃ e, ⟦e⟧ₙ^(chr B) = f,
  { have := (rpartrec.univ_tot ℕ ℕ (primrec.fst.comp primrec.unpair).to_rcomp h'
      (primrec.snd.comp primrec.unpair).to_rcomp), 
    exact exists_index.mp this },
  rcases this with ⟨e, lmm_e⟩,
  have iff : ∀ x, A′ x ↔ B′ (e.mkpair x),
  { simp [Jump, lmm_e] },
  have pi : primrec e.mkpair := primrec₂.mkpair.comp (primrec.const e) (primrec.id),
  have inj : function.injective e.mkpair,
  { intros x y, intros h,
    have : x = (e.mkpair x).unpair.2, simp,
    rw this, rw h, simp },  
  refine ⟨e.mkpair, pi.to_comp, inj, iff⟩,
end

theorem le_compl_of_le {A B : set ℕ} : A ≤₁ B → Aᶜ ≤₁ Bᶜ := λ ⟨f, comp, inj, h⟩,
⟨f, comp, inj, λ x, ⟨λ h₁ h₂, h₁ ((h x).mpr h₂), λ h₁ h₂, h₁ ((h x).mp h₂)⟩⟩

theorem le1_compl_iff {A B : set ℕ} : Aᶜ ≤₁ Bᶜ ↔ A ≤₁ B :=
⟨λ h, by { have := le_compl_of_le h, simp at this, exact this }, le_compl_of_le⟩

open primrec

lemma rre_pred_iff {p : set α} {f : β →. σ} :
  p re_in f ↔ ∃ q : ℕ →. ℕ, q partrec_in f ∧ (∀ x, p x ↔ (q $ encode x).dom) :=
begin
  split; assume h,
  { let q : ℕ →. ℕ := 
      λ n, part.bind (decode α n) (λ a, part.assert (p a) (λ (_ : p a), some 0)),
    have c : q partrec_in f :=
    (computable.decode.of_option.to_rpart).bind (h.comp rcomputable.snd),
    refine ⟨q, c, λ x, _⟩, 
    simp [q, part.some, part.assert, encodek] },
  { rcases h with ⟨q, pq, hq⟩,
    let g : α →. unit := (λ x, (q (encode x)).map (λ x, ())),
    have : g partrec_in f :=
      (pq.comp computable.encode.to_rpart).map (rcomputable.const ()),
    exact (this.of_eq $ λ x, by {
      simp[g], apply part.ext, intros u, simp[hq, dom_iff_mem] }) }
end

lemma rre_pred_iff' {A : set α} {f : β →. σ} :
  A re_in f ↔ ∃ q : α →. ℕ, q partrec_in f ∧ (∀ x, A x ↔ (q x).dom) :=
begin
  split; assume h,
  { let q : α →. ℕ := (λ a, part.assert (A a) (λ (_ : A a), some 0)),
    refine ⟨q, h, λ x, _⟩, 
    simp [q, part.some, part.assert, encodek] },
  { rcases h with ⟨q, pq, hq⟩,
    let g : α →. unit := (λ x, (q x).map (λ x, ())),
    have : g partrec_in f :=
      (pq.comp computable.encode.to_rpart).map (rcomputable.const ()),
    exact (this.of_eq $ λ x, by {
      simp[g], apply part.ext, intros u, simp[hq, dom_iff_mem] }) }
end

lemma rre_pred_iff_exists_index {A : set α} {f : β → σ} :
  A re_in! f ↔ ∃ e : ℕ, A = re_set α ℕ ↑ₒf e :=
⟨λ h, begin
    rcases rre_pred_iff'.mp h with ⟨q, partrec, h⟩,
    rcases exists_index.mp partrec with ⟨e, rfl⟩,
    refine ⟨e, set.ext h⟩ 
  end,
  by {rintros ⟨e, rfl⟩, refine rre_pred_iff'.mpr ⟨⟦e⟧^f, univ_partrec_in, λ x, by simp[re_set]⟩ }⟩

lemma rre_pred.rre {f : α →. σ} {g : β →. τ} {A : set γ} :
  A re_in f → f partrec_in g → A re_in g :=
by simp [rre_pred_iff]; exact λ q pq h pf, ⟨q, pq.trans pf, h⟩

lemma rre_pred.rre' {A : set α} {B : set β} {C : set γ} :
  A re_in! chr B → B ≤ₜ C → A re_in! chr C :=
by simp[classical_iff]; exact rre_pred.rre

theorem t_reducible.rre {A : set α} {B : set β} :
  A ≤ₜ B → A re_in! chr B := λ h,
begin
  have : (λ a, cond (chr A a) (some ()) none) partrec_in! chr B,
  { refine rpartrec.cond (classical_iff.mp h) (rcomputable.const _) rpartrec.none },
  exact (this.of_eq $ λ a,
    by { apply part.ext, simp, intros u, cases C : chr A a; simp at C ⊢; exact C })
end

theorem t_reducible.compl_rre {A : set α} {B : set β} :
  A ≤ₜ B → Aᶜ re_in! chr B := λ h,
begin
  have : (λ a, cond (chr A a) none (some ())) partrec_in! chr B,
  { refine rpartrec.cond (classical_iff.mp h) rpartrec.none (rcomputable.const _) },
  exact (this.of_eq $ λ a, by {
    apply part.ext, simp, intros u, cases C : chr A a; simp at C ⊢, exact C,
    exact not_not.mpr C })
end

theorem t_reducible_iff_rre {A : set α} {B : set β} :
  A ≤ₜ B ↔ A re_in! chr B ∧ Aᶜ re_in! chr B :=
⟨λ h, ⟨h.rre, h.compl_rre⟩, begin
  rintros ⟨h₁, h₂⟩, apply classical_iff.mpr,
  show chr A computable_in! chr B,
  rcases rre_pred_iff'.mp h₁ with ⟨χ, pA, hA⟩,
  rcases rre_pred_iff'.mp h₂ with ⟨χc, pAc, hAc⟩,
  rcases exists_index.mp pA with ⟨e₁, rfl⟩,
  rcases exists_index.mp pAc with ⟨e₂, rfl⟩,
  let f₀ : α → ℕ → option bool :=
    λ x s, ((⟦e₁⟧^(chr B) [s] x : option ℕ).map (λ _, tt)) <|> ((⟦e₂⟧^(chr B) [s] x : option ℕ).map (λ _, ff)),
  let f : α →. bool := λ x, nat.rfind_opt (f₀ x),
  have total : ∀ x, (f x).dom,
  { intros x, simp[f, f₀, nat.rfind_opt_dom], by_cases C : A x,
    { rcases univn_dom_complete.mp ((hA x).mp C) with ⟨n, h_n⟩,
      refine ⟨n, or.inr _⟩,
      rw ←option.some_get h_n, simp only [option.map, option.bind, option.some_orelse] },
    { rcases univn_dom_complete.mp ((hAc x).mp C) with ⟨n, h_n⟩, refine ⟨n, _⟩,
      rw ←option.some_get h_n,
      cases ⟦e₁⟧^(chr B) [n] x with v;
      simp only [option.map, option.bind, option.some_orelse, option.none_orelse], simp, right, refl } },
  let f' : α → bool := λ x, (f x).get (total x),
  have : chr A = f',
  { sorry },
  have mono : ∀ {x : α} {a} {m n : ℕ}, m ≤ n → a ∈ f₀ x m → a ∈ f₀ x n,
  { sorry },
  sorry
 end⟩

theorem rre_Jumpcomputable {A : set α} {B : set ℕ} : A re_in! chr B → A ≤ₜ B′ := 
λ h, classical_iff.mpr 
begin
  show chr A computable_in! chr B′,
  rcases rre_pred_iff.mp h with ⟨a, pa, ha⟩,
  rcases exists_index.mp pa with ⟨e, he⟩,
  let f : α → bool := (λ x, chr B′ (e.mkpair (encode x))),
  have l0 : f computable_in (chr B′ : ℕ →. bool) :=
    rcomputable.refl.comp (primrec₂.mkpair.comp
      (primrec.const e) primrec.encode).to_rcomp,
  have l1 : f = chr A,
  { funext x, simp[f, Jump, chr_ext, set.set_of_app_iff, he, ha], },
  show chr A computable_in! chr B′, from (l0.of_eq $ by simp[l1])
end

theorem rre_iff_one_one_reducible {A B : set ℕ} : A re_in! chr B ↔ A ≤₁ B′ := 
⟨ begin
    assume h, show A ≤₁ B′,
    rcases rre_pred_iff.mp h with ⟨a, pa, ha⟩,
    rcases exists_index.mp pa with ⟨e, eqn_e⟩,
    have lmm1 : primrec e.mkpair := primrec₂.mkpair.comp (primrec.const _) primrec.id,
    have lmm2 : function.injective e.mkpair,
    { intros x y h,
      have : x = (e.mkpair x).unpair.2, simp,
      rw this, rw h, simp },  
    have lmm3 : ∀ n, A n ↔ B′ (e.mkpair n),
    { simp[Jump, chr_ext, set.set_of_app_iff, eqn_e, ha], },  
    refine ⟨e.mkpair, lmm1.to_comp, lmm2, lmm3⟩,
  end,
  begin
    assume h, show A re_in! chr B,
    rcases h with ⟨i, ci, inj, hi⟩,
    apply rre_pred_iff.mpr,
    let q : ℕ →. ℕ := (λ x, ⟦(i x).unpair.1⟧ₙ^(chr B) (i x).unpair.2),
    have lmm : q partrec_in! chr B,
    { refine rpartrec.univ_tot _ _
      (computable.fst.comp (primrec.unpair.to_comp.comp ci)).to_rcomp
      rcomputable.refl
      (computable.snd.comp (primrec.unpair.to_comp.comp ci)).to_rcomp },
    have lmm1 : ∀ n, A n ↔ (q n).dom,
    { intros x, simp [hi, q, Jump] },
    refine ⟨q, lmm, lmm1⟩,
  end⟩

theorem re_many_one_reducible_to_0' {A : set ℕ} : r.e. A ↔ A ≤₁ ∅′ :=
⟨λ h, rre_iff_one_one_reducible.mp (h.to_rpart),
 λ h, (rre_iff_one_one_reducible.mpr h).re0 ⟩

theorem re_pred_Jump_0 : r.e. ∅′ :=
re_many_one_reducible_to_0'.mpr (by refl)

lemma dom_rre (f : α →. σ) : {x | (f x).dom} re_in f :=
begin
  let g := (λ a, (f a).map (λ x, ())),
  have := rpartrec.refl.map ((computable.const ()).comp computable.snd).to_rcomp.to₂,
  exact (this.of_eq $ λ x, by { rw set.set_of_app_iff, simp, 
    apply part.ext, intros a, simp [dom_iff_mem] })
end

theorem exists_rre [inhabited β] {p : α → β → Prop} {g : γ → τ} :
  {x : α × β | p x.1 x.2} re_in! g → {x | ∃ y, p x y} re_in! g := λ h,
begin
  have := rpartrec.exists_index.mp h,
  rcases this with ⟨e, eqn_e⟩,
  have eqn_e1 : ∀ x y, p x y ↔ (⟦e⟧^g (x, y) : part unit).dom,
  { simp [eqn_e, part.assert, part.some] },
  let p' := (λ x : α, nat.rfind (λ u, (⟦e⟧^g [u.unpair.2]
    (x, (decode β u.unpair.1).get_or_else (default β)) : option unit).is_some)),
  have lmm : ∀ x, (∃ y, p x y) ↔ (p' x).dom,
  { intros x, simp only [p'], split,
    { rintros ⟨y, hb⟩, rw eqn_e1 at hb,
      apply rfind_dom_total,
      simp [part.dom_iff_mem, part.some] at hb ⊢, rcases hb with ⟨z, hz⟩,
      rcases univn_complete.mp hz with ⟨s, hs⟩,
      use (encode y).mkpair s,
      simp [hs] },
    { simp, intros u h0 h1, 
      use (decode β u.unpair.fst).get_or_else (default β),
      cases e : (⟦e⟧^g [u.unpair.snd] (x, 
        (decode β u.unpair.fst).get_or_else (default β)) : option unit) with v,
      { exfalso, simp [e] at h0, exact h0 },
      have := univn_sound e, simp [eqn_e1, this] } },
  have eqn : {x | ∃ y, p x y} = {x | (p' x).dom},
  { apply set.ext, simp [lmm] },
  have : p' partrec_in! g,
  { apply rpartrec.rfind,
    refine primrec.option_is_some.to_rcomp.comp
      (rcomputable.univn_tot _ _ 
        (primrec.const _).to_rcomp
        rcomputable.refl (snd.comp $ primrec.unpair.comp snd).to_rcomp _),
    have := ((fst.pair (option_get_or_else.comp 
      (primrec.decode.comp $ fst.comp $ unpair.comp snd)
      (const (default β))))), exact this.to_rcomp },
  rw eqn,
  show {x | (p' x).dom} re_in! g,
  from (dom_rre p').rre this
end

theorem rre_compl_of_rre {A B : set ℕ} :
  A re_in! chr B → Aᶜ re_in! chr B′ := λ h,
begin
  have lmm₁ : Aᶜ ≤₁ B′ᶜ,
  { simp[le1_compl_iff], exact rre_iff_one_one_reducible.mp h },
  have lmm₂ : B′ᶜ ≤₁ B′′, from rre_iff_one_one_reducible.mp (t_reducible.rre (reducible_compl B′)),
  exact rre_iff_one_one_reducible.mpr (lmm₁.trans lmm₂)
end

lemma rre_pred.rre_of_le {A : set α} {B : set β} {C : set γ} :
  A re_in! chr B → C ≤₀ A → C re_in! chr B := λ h ⟨f, comp, fh⟩,
begin
  rcases rre_pred_iff'.mp h with ⟨q, partrec, qh⟩,
  refine rre_pred_iff'.mpr ⟨q ∘ f, partrec.comp comp.to_rcomp, λ x, by simp[fh, qh]⟩,
end

theorem exists_reducible [inhabited β] {p : α → β → Prop} {A : set ℕ} :
  {x : α × β | p x.1 x.2} ≤ₜ A → {x | ∃ y, p x y} ≤ₜ A′ :=
λ h, rre_Jumpcomputable (exists_rre h.rre)

theorem forall_reducible [inhabited β] {p : α → β → Prop} {A : set ℕ} :
  {x : α × β | p x.1 x.2} ≤ₜ A → {x | ∀ y, p x y} ≤ₜ A′ := λ h,
begin
  have : {x | ∀ y, p x y}ᶜ ≤ₜ A′,
  { have : {x | ∃ y, ¬p x y} ≤ₜ A′,
    { apply exists_reducible, 
      have := (equiv_compl {x : α × β | p x.1 x.2}).1.trans (h.of_eq $ by { intros a, simp }),
      exact (this.of_eq $ λ a, by refl) },
    exact (this.of_eq $ λ a, by { simp, exact not_forall.symm }) },
  apply (equiv_compl {x | ∀ y, p x y}).2.trans this
end

def Kleene (A : set ℕ) : set ℕ := {x | (⟦x⟧ₙ^(chr A) x).dom}

def Tot (A : set ℕ) : set ℕ := {e | ∀ x, (⟦e⟧ₙ^(chr A) x).dom}

def Unbound (A : set ℕ) : set ℕ := {e | ∀ x, ∃ y, x ≤ y ∧ (⟦e⟧ₙ^(chr A) y).dom}

def Rec (A : set ℕ) : set ℕ := {e | W⟦e⟧ₙ^(chr A) ≤ₜ A}

theorem Kleene_equiv_Jump (A : set ℕ) : Kleene A ≡ₜ A′ :=
⟨classical_iff.mpr 
  begin
    show chr (Kleene A) computable_in! chr A′,
    let f := (λ n : ℕ, chr A′ (n.mkpair n)),
    have : chr (Kleene A) = f,
    { funext n, apply chr_ext.mpr,
      simp [Kleene, f, Jump] },
    rw this,
    have := rcomputable.refl.comp
      (primrec₂.mkpair.comp primrec.id primrec.id).to_rcomp,
    exact this
  end, classical_iff.mpr
  begin
    show chr A′ computable_in! chr (Kleene A),
    let t := (λ x : ℕ × (ℕ × ℕ), ⟦x.1⟧ₙ^(chr A) x.2.1),
    have : ∃ e, ⟦e⟧^(chr A) = t,
    { have : t partrec_in! chr A :=
        (rpartrec.univ_tot ℕ ℕ rcomputable.fst rcomputable.refl (fst.comp snd).to_rcomp),
      exact exists_index.mp this },
    rcases this with ⟨e, eqn_e⟩,
    let k := (λ n m : ℕ, curry (curry e n) m),
    have eqn_k : ∀ z i x, ⟦k i x⟧ₙ^(chr A) z = ⟦i⟧ₙ^(chr A) x,
    { intros z i x, simp [k, eqn_e] },
    let f := (λ x : ℕ, chr (Kleene A) (k x.unpair.1 x.unpair.2)),
    have : chr A′ = f,
    { funext n, apply chr_ext.mpr,
      simp [Kleene, f, Jump, eqn_k, eqn_e] },
    rw this,
    have : primrec₂ k := curry_prim.comp
      (curry_prim.comp (const e) fst) snd,
    have := rcomputable.refl.comp
      (this.comp (fst.comp primrec.unpair)
      (snd.comp primrec.unpair)).to_rcomp,
    exact this
  end⟩

theorem Tot_equiv_Jump2 (A : set ℕ) : Tot A ≤ₜ A′′ :=
begin
  have : Tot A = {e | ∀ x, ∃ s, (⟦e⟧ₙ^(chr A) [s] x).is_some},
  { simp[Tot, rpartrec.univn_dom_complete] },
  rw this,
  refine forall_reducible (exists_reducible $ classical_iff.mpr _),
  simp, 
  refine option_is_some.to_rcomp.comp (rcomputable.univn_tot _ _
    (fst.comp fst).to_rcomp rcomputable.refl snd.to_rcomp (snd.comp fst).to_rcomp),
end

theorem Unbound_equiv_Jump2 (A : set ℕ) : Unbound A ≤ₜ A′′ :=
begin
  have : Unbound A = {e | ∀ x, ∃ y : ℕ × ℕ, x ≤ y.2 ∧ (⟦e⟧ₙ^(chr A) [y.1] y.2).is_some},
  { simp[Unbound, rpartrec.univn_dom_complete], funext n,
    simp, refine forall_congr (λ x, _), split,
    { rintros ⟨y, eqn, s, h⟩, refine ⟨s, y, eqn, h⟩ },
    { rintros ⟨s, y, eqn, h⟩, refine ⟨y, eqn, s, h⟩ } },
  rw this,
  refine forall_reducible (exists_reducible $ classical_iff.mpr _),
  let f := (λ x : (ℕ × ℕ) × ℕ × ℕ, to_bool (x.fst.snd ≤ x.snd.snd) &&
    (⟦x.fst.fst⟧ₙ^(chr A) [x.snd.fst] x.snd.snd).is_some),
  have : f computable_in! chr A,
  { refine (primrec.dom_bool₂ (&&)).to_rcomp.comp₂'
      (primrec₂.comp primrec.nat_le (snd.comp fst) (snd.comp snd)).to_rcomp
      (primrec.option_is_some.to_rcomp.comp (rcomputable.univn_tot _ _
        (fst.comp fst).to_rcomp rcomputable.refl (fst.comp snd).to_rcomp (snd.comp snd).to_rcomp)) },
  exact (this.of_eq $ λ x, by symmetry; simp[f, chr_iff])
end

theorem Rec_equiv_Jump3 (A : set ℕ) : Rec A ≤ₜ A′′′ :=
begin
  have : Rec A = {e : ℕ | ∃ i, ∀ x, ∃ s, (⟦i⟧ᵪ^(chr A) [s] x = some tt ↔ (⟦e⟧ₙ^(chr A) [s] x).is_some)},
  { simp[Rec, re_set], ext e, simp, sorry }, sorry
end

lemma rre_enumeration_iff {A : set α} {f : β → σ} (h : ∃ a, a ∈ A) :
  A re_in! f → (∃ e : ℕ → α, e computable_in! f ∧ (∀ x, x ∈ A ↔ ∃ n, e n = x)) :=
begin
  rcases h with ⟨a₀, hyp_a₀⟩,
  { intros hyp,
    rcases rre_pred_iff.mp hyp with ⟨q, hyp_q, hyp_q1⟩,
    let q' := (λ x : α, q (encode x)),
    have hyp_q' : q' partrec_in! f := hyp_q.comp primrec.encode.to_rcomp,
    rcases exists_index.mp hyp_q' with ⟨i, eqn_i⟩,
    let e := (λ n : ℕ, cond (⟦i⟧^f [n.unpair.1] 
      ((decode α n.unpair.2).get_or_else a₀) : option ℕ).is_some
      ((decode α n.unpair.2).get_or_else a₀) a₀),
    have lmm1 : e computable_in! f,
    { refine rcomputable.cond
        (option_is_some.to_rcomp.comp (rcomputable.univn_tot _ _
          (rcomputable.const _)
          rcomputable.refl
          (fst.comp unpair).to_rcomp
          (option_get_or_else.comp (primrec.decode.comp $ snd.comp unpair) (const _)).to_rcomp))
        (option_get_or_else.comp (primrec.decode.comp $ snd.comp unpair)
          (const _)).to_rcomp (const _).to_rcomp },
    have lmm2 : ∀ x, x ∈ A ↔ ∃ n, e n = x,
    { simp [e], intros a, split,
      { intros hyp_a,
        have : ∃ y : ℕ, y ∈ (⟦i⟧^f a : part ℕ),
        { simp [←part.dom_iff_mem, eqn_i, q', ←hyp_q1], exact hyp_a },
        rcases this with ⟨y, lmm_y⟩,
        have := univn_complete.mp lmm_y, rcases this with ⟨s, lmm_s⟩,
        refine ⟨s.mkpair (encode a), _⟩, simp, simp[lmm_s] },
      { rintros ⟨n, hyp_n⟩,
        cases C : (⟦i⟧^f [n.unpair.fst] ((decode α n.unpair.snd).get_or_else a₀) : option ℕ) with v;
        simp[C] at hyp_n, simp[←hyp_n], exact hyp_a₀,
        suffices : (⟦i⟧^f a : part ℕ).dom,
        { simp[eqn_i, q', ←hyp_q1] at this, exact this },
        have := univn_sound C,
        simp[←hyp_n, this] } },
    refine ⟨e, lmm1, lmm2⟩ }
end

lemma re_enumeration_iff {A : set α} {f : β → σ} (h : ∃ a, a ∈ A) :
  r.e. A → ∃ e : ℕ → α, computable e ∧ (∀ x, x ∈ A ↔ ∃ n, e n = x) := λ hyp,
by { rcases rre_enumeration_iff h (hyp.to_rpart_in ↑ᵣ(@id ℕ)) with ⟨e, lmm1, lmm2⟩,
     refine ⟨e, rcomputable.le_comp_comp lmm1 computable.id, lmm2⟩ }

mutual def pie_pred, sigma_pred
with pie_pred : ℕ → set ℕ → Prop
| 0       A := computable_pred A
| (n + 1) A := ∃ B : set ℕ, sigma_pred n B ∧ A = {x | ∀ y, (x.mkpair y) ∈ B}
with sigma_pred : ℕ → set ℕ → Prop
| 0       A := computable_pred A
| (n + 1) A := ∃ B : set ℕ, pie_pred n B ∧ A = {x | ∃ y, (x.mkpair y) ∈ B}

prefix `𝚷⁰`:max := pie_pred

prefix `𝚺⁰`:max := sigma_pred

def delta_pred (n : ℕ) (A : set ℕ) : Prop := 𝚷⁰n A ∧ 𝚺⁰n A

prefix `𝚫⁰`:max := delta_pred

@[simp] lemma pie_pred0_iff {A : set ℕ} : 𝚷⁰0 A ↔ computable_pred A := by simp[pie_pred]

@[simp] lemma sigma_pred0_iff {A : set ℕ} : 𝚺⁰0 A ↔ computable_pred A := by simp[sigma_pred]

lemma pie_pred2_iff {A : set ℕ} {n : ℕ} :
  𝚷⁰(n + 2) A ↔ ∃ B : set ℕ, 𝚷⁰n B ∧ A = {x | ∀ y, ∃ z, (x.mkpair y).mkpair z ∈ B} :=
by { simp[sigma_pred, pie_pred], split,
     { rintros ⟨B₁, ⟨B₂, sigma, rfl⟩, rfl⟩, refine ⟨B₂, sigma, by refl⟩ },
     { rintros ⟨B₁, sigma, rfl⟩, refine ⟨_, ⟨B₁, sigma, rfl⟩, by refl⟩ } }

lemma sigma_pred2_iff {A : set ℕ} {n : ℕ} :
  𝚺⁰(n + 2) A ↔ ∃ B : set ℕ, 𝚺⁰n B ∧ A = {x | ∃ y, ∀ z, (x.mkpair y).mkpair z ∈ B} :=
by { simp[sigma_pred, pie_pred], split,
     { rintros ⟨B₁, ⟨B₂, sigma, rfl⟩, rfl⟩, refine ⟨B₂, sigma, by refl⟩ },
     { rintros ⟨B₁, sigma, rfl⟩, refine ⟨_, ⟨B₁, sigma, rfl⟩, by refl⟩ } }

lemma arith_hie_compl : ∀ {n : ℕ} {A : set ℕ},
  𝚷⁰n A ↔ 𝚺⁰n Aᶜ
| 0       A := by { simp[degree0'], exactI ⟨λ h, (equiv_compl A).trans h, λ h, (equiv_compl A).symm.trans h⟩ }
| (n + 1) A := by { simp[sigma_pred, pie_pred], split,
    { rintros ⟨B, sigma, rfl⟩,
      refine ⟨Bᶜ, (@arith_hie_compl n Bᶜ).mpr (by simp[sigma]), by simp[set.compl_set_of]⟩ },
    { rintros ⟨B, pie, eqn⟩,
      refine ⟨Bᶜ, (@arith_hie_compl n B).mp pie, 
        by rw ←(compl_compl A); rw eqn; simp[set.compl_set_of]⟩ } }

lemma pie_pred.many_one : ∀ {n : ℕ} {A B : set ℕ} (pie : 𝚷⁰n B) (le : A ≤₀ B), 𝚷⁰n A
| 0       A B pie le := by { simp at*, exact le_computable_computable le.to_turing pie }
| 1       A B pie ⟨f, f_comp, le⟩ := by { simp[pie_pred] at pie,
    rcases pie with ⟨B', sigma, rfl⟩,
    let C : set ℕ := {x | (f x.unpair.1).mkpair x.unpair.2 ∈ B'},
    have : C ≤₀ B',
    { refine ⟨λ x, (f x.unpair.1).mkpair x.unpair.2, _, λ x, by simp[C]; refl⟩,
      refine primrec₂.mkpair.to_comp.comp (f_comp.comp (fst.comp unpair).to_comp) (snd.comp unpair).to_comp },
    have sigma' : computable_pred C, from le_computable_computable this.to_turing sigma,
    have : A = {x | ∀ y, x.mkpair y ∈ C}, { simp[C], exact set.ext le },
    simp [pie_pred], refine ⟨C, sigma', this⟩ }
| (n + 2) A B pie ⟨f, f_comp, le⟩ := by {
    rcases pie_pred2_iff.mp pie with ⟨B', pie', rfl⟩,
    let C : set ℕ := {x | ((f x.unpair.1.unpair.1).mkpair x.unpair.1.unpair.2).mkpair x.unpair.2 ∈ B'},
    have : C ≤₀ B',
    { refine ⟨λ x, ((f x.unpair.1.unpair.1).mkpair x.unpair.1.unpair.2).mkpair x.unpair.2,
        _, λ x, by simp[C]; refl⟩,
      refine primrec₂.mkpair.to_comp.comp
        (primrec₂.mkpair.to_comp.comp (f_comp.comp (fst.comp $ unpair.comp $ fst.comp unpair).to_comp)
        (snd.comp $ unpair.comp $ fst.comp unpair).to_comp) (snd.comp unpair).to_comp },    
    have IH : 𝚷⁰n C, from pie_pred.many_one pie' this,
    have : A = {x | ∀ y, ∃ z, (x.mkpair y).mkpair z ∈ C},
    { simp[C], exact set.ext le },
    refine pie_pred2_iff.mpr ⟨C, IH, this⟩ }

lemma sigma_pred.many_one : ∀ {n : ℕ} {A B : set ℕ} (sigma : 𝚺⁰n B) (le : A ≤₀ B), 𝚺⁰n A
| 0       A B sigma le := by { simp at*, exact le_computable_computable le.to_turing sigma }
| 1       A B sigma ⟨f, f_comp, le⟩ := by { simp[sigma_pred] at sigma,
    rcases sigma with ⟨B', pie, rfl⟩,
    let C : set ℕ := {x | (f x.unpair.1).mkpair x.unpair.2 ∈ B'},
    have : C ≤₀ B',
    { refine ⟨λ x, (f x.unpair.1).mkpair x.unpair.2, _, λ x, by simp[C]; refl⟩,
      refine primrec₂.mkpair.to_comp.comp (f_comp.comp (fst.comp unpair).to_comp) (snd.comp unpair).to_comp },
    have pie' : computable_pred C, from le_computable_computable this.to_turing pie,
    have : A = {x | ∃ y, x.mkpair y ∈ C}, { simp[C], exact set.ext le },
    simp[sigma_pred], refine ⟨C, pie', this⟩ }
| (n + 2) A B sigma ⟨f, f_comp, le⟩ := by {
    rcases sigma_pred2_iff.mp sigma with ⟨B', sigma', rfl⟩,
    let C : set ℕ := {x | ((f x.unpair.1.unpair.1).mkpair x.unpair.1.unpair.2).mkpair x.unpair.2 ∈ B'},
    have : C ≤₀ B',
    { refine ⟨λ x, ((f x.unpair.1.unpair.1).mkpair x.unpair.1.unpair.2).mkpair x.unpair.2,
        _, λ x, by simp[C]; refl⟩,
      refine primrec₂.mkpair.to_comp.comp
        (primrec₂.mkpair.to_comp.comp (f_comp.comp (fst.comp $ unpair.comp $ fst.comp unpair).to_comp)
        (snd.comp $ unpair.comp $ fst.comp unpair).to_comp) (snd.comp unpair).to_comp },    
    have IH : 𝚺⁰n C, from sigma_pred.many_one sigma' this,
    have : A = {x : ℕ | ∃ (y : ℕ), ∀ (z : ℕ), (x.mkpair y).mkpair z ∈ C},
    { simp[C], exact set.ext le },
    refine sigma_pred2_iff.mpr ⟨C, IH, this⟩ }

lemma pie_pred_iff {p : ℕ → ℕ → Prop} {n : ℕ}
  (h : 𝚺⁰n {x | p x.unpair.1 x.unpair.2}) : 𝚷⁰(n + 1) {x | ∀ y, p x y} :=
  by simp[pie_pred]; refine ⟨{x : ℕ | p (nat.unpair x).fst (nat.unpair x).snd}, h, by simp⟩

lemma sigma_pred_iff {p : ℕ → ℕ → Prop} {n : ℕ}
  (h : 𝚷⁰n {x | p x.unpair.1 x.unpair.2}) : 𝚺⁰(n + 1) {x | ∃ y, p x y} :=
  by simp[sigma_pred]; refine ⟨{x : ℕ | p (nat.unpair x).fst (nat.unpair x).snd}, h, by simp⟩

lemma pie_pred_bforall {p : ℕ → ℕ → Prop} {n : ℕ} {b : ℕ}
  (h : 𝚺⁰n {x | p x.unpair.1 x.unpair.2}) : 𝚺⁰n {x | ∀ y < b, p x y} :=
  by {  }

lemma sigma_pred.exists {n : ℕ} {A : set ℕ} (h : 𝚺⁰(n + 1) A) :
  𝚺⁰(n + 1) {x | ∃ y, (x.mkpair y) ∈ A} :=
begin
  simp[sigma_pred] at h ⊢,
  rcases (h) with ⟨B, pie, rfl⟩,
  simp,
  let B' : set ℕ := {x | (x.unpair.1.mkpair x.unpair.2.unpair.1).mkpair x.unpair.2.unpair.2 ∈ B},
  have eqn : {x : ℕ | ∃ y n, ((x.mkpair y).mkpair n) ∈ B} = {x | ∃ y : ℕ, (x.mkpair y) ∈ B' },
  { apply set.ext, intros x, simp[B'], split,
    { rintros ⟨y, n, mem⟩, refine ⟨y.mkpair n, _⟩, simp[mem] },
    { rintros ⟨y, mem⟩, refine ⟨y.unpair.1, y.unpair.2, mem⟩ } },
  have le : B' ≤₀ B,
  { refine ⟨λ x, (x.unpair.1.mkpair x.unpair.2.unpair.1).mkpair x.unpair.2.unpair.2, _, λ x, by simp[B']; refl⟩,
    refine (primrec₂.mkpair.comp
      (primrec₂.mkpair.comp (fst.comp unpair) $ fst.comp $ unpair.comp $ snd.comp unpair)
      (snd.comp $ unpair.comp $ snd.comp unpair)).to_comp },
  refine ⟨B', pie.many_one le, eqn⟩
end

lemma sigma_pred.exists' {n : ℕ} {p : ℕ → ℕ → Prop} (h : 𝚺⁰(n + 1) {x | p x.unpair.1 x.unpair.2}) :
  𝚺⁰(n + 1) {x | ∃ y, p x y} :=
by have := h.exists; simp at this; exact this

lemma sigma_pred.exists'' [inhabited α] {n : ℕ} {p : ℕ → α → Prop}
  (h : 𝚺⁰(n + 1) {x | p x.unpair.1 ((encodable.decode α x.unpair.2 ).get_or_else (default α))}) :
  𝚺⁰(n + 1) {x | ∃ y, p x y} :=
by { have := h.exists, simp at this, sorry }

lemma pie_pred.forall {n : ℕ} {A : set ℕ} (h : 𝚷⁰(n + 1) A) :
  𝚷⁰(n + 1) {x | ∀ y, (x.mkpair y) ∈ A} :=
by simp[arith_hie_compl, set.compl_set_of] at h ⊢; exact h.exists

lemma pie_pred.forall' {n : ℕ} {p : ℕ → ℕ → Prop} (h : 𝚷⁰(n + 1) {x | p x.unpair.1 x.unpair.2}) :
  𝚷⁰(n + 1) {x | ∀ y, p x y} :=
by have := h.forall; simp at this; exact this

lemma sigma_pred1_iff_re {A : set ℕ} : 𝚺⁰1 A ↔ r.e. A :=
begin
  simp[sigma_pred, ←rre_in_0_iff_re], split,
  { rintros ⟨B, comp, rfl⟩, refine exists_rre (t_reducible.rre _),
    have : {x : ℕ × ℕ | x.1.mkpair x.2 ∈ B} ≤ₜ B,
      from classical_iff.mpr (rcomputable.refl.comp (primrec₂.mkpair.comp fst snd).to_rcomp),
    exact this.trans ((degree0' B).mp comp).1 },
  { intros h,
    rcases rre_pred_iff_exists_index.mp h with ⟨e, rfl⟩,
    let B : set ℕ := {x | (⟦e⟧ₙ^(chr ∅ : ℕ → bool) [x.unpair.2] x.unpair.1).is_some},
    have lmm₁ : computable_pred B,
    { refine computable_pred_iff_le.mpr (classical_iff.mpr _),
      have : (λ x : ℕ, (⟦e⟧ₙ^(chr ∅ : ℕ → bool) [x.unpair.2] x.unpair.1).is_some) computable_in! chr (∅ : set ℕ),
        from primrec.option_is_some.to_rcomp.comp
          (rcomputable.univn_tot _ _ (rcomputable.const _) rcomputable.refl (snd.comp unpair).to_rcomp (fst.comp unpair).to_rcomp ),
      exact this.of_eq (λ x, by simp[B]) },
    have lmm₂ : W⟦e⟧ₙ^(chr (∅ : set ℕ)) = {x | ∃ y, x.mkpair y ∈ B},
    { refine set.ext (λ x, _), simp[B], exact univn_dom_complete },
    exact ⟨B, lmm₁, lmm₂⟩ }
end

lemma pie_pred1_iff_co_re {A : set ℕ} : 𝚷⁰1 A ↔ r.e. Aᶜ :=
by simp[arith_hie_compl, sigma_pred1_iff_re]

lemma sigma_Jump_of_pie {n : ℕ} {A : set ℕ} (sigma : 𝚺⁰ n A) : 𝚺⁰ (n + 1) A′ :=
begin
  simp[Jump], sorry
end

theorem sigma_complete : ∀ {n : ℕ} {A : set ℕ},
  𝚺⁰(n + 1) A ↔ A re_in! chr (Jump_itr n ∅)
| 0       A := by simp[rre_in_0_iff_re]; exact sigma_pred1_iff_re
| (n + 1) A := begin
    have IH_sigma : ∀ {A}, 𝚺⁰(n + 1) A ↔ A re_in! chr (Jump_itr n ∅), from @sigma_complete n,
    have IH_pie : ∀ {A}, 𝚷⁰(n + 1) A ↔ Aᶜ re_in! chr (Jump_itr n ∅),
    { intros A, simp[arith_hie_compl, IH_sigma] },
    split, 
    { simp[sigma_pred], rintros B pie rfl, refine exists_rre _,
      have lmm₁ : B re_in! chr (Jump_itr n ∅)′,
      { have := rre_compl_of_rre (IH_pie.mp pie), simp at this, exact this },
      have lmm₂ : {x : ℕ × ℕ | nat.mkpair x.fst x.snd ∈ B} ≤₀ B,
        from ⟨λ x, nat.mkpair x.fst x.snd, (primrec₂.mkpair.comp fst snd).to_comp, by simp[set.mem_def]⟩,
      exact rre_pred.rre_of_le lmm₁ lmm₂ },
    { intros h, simp at h,
      have : 𝚺⁰(n + 1) (Jump_itr n ∅)′, from IH_sigma.mpr (rre_iff_one_one_reducible.mpr (by refl)),
      refine (sigma_Jump_of_pie this).many_one (rre_iff_one_one_reducible.mp h).to_many_one }
  end


lemma computable_pred_iff_chr_computable {A : set ℕ} : computable_pred A ↔ computable (chr A) :=
begin
  simp[computable_pred_iff_le, classical_iff],
  split; intros h, { refine rcomputable.le_comp_comp h ((computable.const ff).of_eq (by { simp[has_emptyc.emptyc] })), },
  { exact h.to_rcomp }
end

lemma re_Join_of_re_re {A B : set ℕ} (hA : r.e. A) (hB : r.e. B) : r.e. Join₂ A B :=
begin
  simp[Join₂, Join, ←sigma_pred1_iff_re, sigma_pred, computable_pred_iff_chr_computable] at *,
  rcases hA with ⟨A, hA, rfl⟩,
  rcases hB with ⟨B, hB, rfl⟩,
  let C : set ℕ := {n : ℕ |
    if (nat.unpair n).1.unpair.2 = 0 then nat.mkpair n.unpair.1.unpair.1 n.unpair.2 ∈ A else
    if (nat.unpair n).1.unpair.2 = 1 then nat.mkpair n.unpair.1.unpair.1 n.unpair.2 ∈ B else false },
  refine ⟨C, by { simp[C],
    suffices :
      computable
      (λ n, if (nat.unpair n).1.unpair.2 = 0 then chr A (nat.mkpair n.unpair.1.unpair.1 n.unpair.2) else
            if (nat.unpair n).1.unpair.2 = 1 then chr B (nat.mkpair n.unpair.1.unpair.1 n.unpair.2) else ff),
    exact this.of_eq (λ n, by { by_cases C₁ : (nat.unpair (nat.unpair n).fst).snd = 0; simp[C₁, set.mem_def, chr_eq_to_bool],
      by_cases C₂ : (nat.unpair (nat.unpair n).fst).snd = 1; simp[C₂] }),
    refine rcomputable.computable_of_rcomp (rcomputable.ite
      (rcomputable.to_bool_eq ℕ
        (rcomputable.snd.comp (rcomputable.nat_unpaired.comp (rcomputable.fst.comp rcomputable.nat_unpaired)))
        (rcomputable.const 0))
      (hA.to_rcomp.comp (rcomputable₂.comp rpartrec.some
        (rcomputable.fst.comp (rcomputable.nat_unpaired.comp (rcomputable.fst.comp rcomputable.nat_unpaired)))
        (rcomputable.snd.comp rcomputable.nat_unpaired))) _),
    refine rcomputable.ite
      (rcomputable.to_bool_eq ℕ
        (rcomputable.snd.comp (rcomputable.nat_unpaired.comp (rcomputable.fst.comp rcomputable.nat_unpaired)))
        (rcomputable.const 1)) (hB.to_rcomp.comp
      (rcomputable₂.comp rpartrec.some
        (rcomputable.fst.comp (rcomputable.nat_unpaired.comp (rcomputable.fst.comp rcomputable.nat_unpaired)))
        (rcomputable.snd.comp rcomputable.nat_unpaired))) (rcomputable.const ff) },
  by { ext x, simp, cases (nat.unpair x).snd with n; simp,
    { cases n with n; simp }}⟩,
end

end classical