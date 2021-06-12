import coding function
import computability.reduce
open encodable denumerable roption

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

@[simp] theorem chr_iff {α} (A : set α) (x : α) : chr A x = tt ↔ A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

@[simp] theorem chr_ff_iff {α} (A : set α) (x : α) : chr A x = ff ↔ ¬A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

theorem to_bool_chr_eq {α} (A : set α) (x : α) (D : decidable (A x)) :
  to_bool (A x) = chr A x :=
by { cases (@decidable.em (A x) D) with h,
     simp[to_bool_tt h, (chr_iff _ _).2 h],
     simp[to_bool_ff h, (chr_ff_iff _ _).2 h] }

theorem chr_ext {α β} {A : set α} {B : set β} {x y} : chr A x = chr B y ↔ (A x ↔ B y) :=
begin
    split,
  { assume h,
    cases e : chr A x, 
    have ax := (chr_ff_iff _ _).mp e,
    have bx := (chr_ff_iff B y).mp (by simp[←h, e]), simp[ax,bx],
    have ax := (chr_iff _ _).mp e,
    have bx := (chr_iff B y).mp (by simp[←h, e]), simp[ax,bx] },
  { assume h, 
    cases e : chr B y,
    have bx := (chr_ff_iff _ _).mp e,
    exact (chr_ff_iff A x).mpr (by simp [h, bx]),
    have bx := (chr_iff _ _).mp e,
    exact (chr_iff A x).mpr (by simp [h, bx]) }
end

def rre_pred {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  (p : set α) (f : β →. σ) : Prop :=
(λ a, roption.assert (p a) (λ _, roption.some ())) partrec_in f

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

def t_reducible {α β} [primcodable α] [primcodable β] (A : set α) (B : set β)  : Prop := 
∃ [D0 : decidable_pred A] [D1 : decidable_pred B],
by exactI (λ x, to_bool (A x)) computable_in! (λ x, to_bool (B x)) 

infix ` ≤ₜ `:1000 := t_reducible

notation A` ≰ₜ `B:1000 := ¬A ≤ₜ B

def t_reducible_lt {α β} [primcodable α] [primcodable β] (A : set α) (B : set β) : Prop :=
A ≤ₜ B ∧ ¬B ≤ₜ A

infix ` <ₜ `:1000 := t_reducible_lt

def t_reducible_equiv {α β} [primcodable α] [primcodable β] (A : set α) (B : set β) : Prop :=
A ≤ₜ B ∧ B ≤ₜ A

infix ` ≡ₜ `:1000 := t_reducible_equiv

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

theorem many_one_reducible.to_turing {A : set α} {B : set β} [DA : decidable_pred A] [DB : decidable_pred B] :
  A ≤₀ B → A ≤ₜ B := λ h,
⟨DA, DB, by { rcases h with ⟨f, cf, hf⟩,
 exact ((rcomputable.refl.comp (cf.to_rcomp)).of_eq $ λ n, by simp [hf]) }⟩

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

theorem degree0 (A : set α) :
  computable_pred A ↔ A ≡ₜ (∅ : set β) := 
⟨λ ⟨D, h⟩, ⟨computable_le _ ⟨D, h⟩, @computable_le _ _ _ _ _ _ D computable_0⟩,
 λ ⟨h, _⟩, le_computable_computable h computable_0⟩

def Join (A : ℕ → set ℕ) : set ℕ := {x | x.unpair.1 ∈ A x.unpair.2}

prefix `⨁`:80 := Join

theorem Join_many_one_reducible (A : ℕ → set ℕ) [D : ∀ n, decidable_pred (A n)] (n) : A n ≤₀ ⨁A :=
begin
  let f := (λ m : ℕ, m.mkpair n),
  have cf : computable f := (primrec₂.mkpair.comp primrec.id (primrec.const n)).to_comp,
  refine ⟨f, cf, _⟩,
  { intros x, simp [Join], refl }
end

section classical
local attribute [instance, priority 0] classical.prop_decidable
open rpartrec

theorem cond_if_eq {α β} (p : set α) (x) (a b : β) :
  cond (chr p x) a b = if p x then a else b :=
by {by_cases h : p x; simp [h], simp [(chr_iff p x).mpr h], simp [(chr_ff_iff p x).mpr h] }

def jump (A : set ℕ) : set ℕ := {x | (⟦x.unpair.1⟧ₙ^(chr A) x.unpair.2).dom}

def Kleene (A : set ℕ) : set ℕ := {x | (⟦x⟧ₙ^(chr A) x).dom}

def Tot (A : set ℕ) : set ℕ := {e | ∀ x, (⟦e⟧ₙ^(chr A) x).dom}

def Inf (A : set ℕ) : set ℕ := {e | ∀ x, ∃ y, x ≤ y ∧ (⟦e⟧ₙ^(chr A) y).dom}

notation A`′`:1200 := jump A

def jump_itr : ℕ → set ℕ → set ℕ
| 0     A := A
| (n+1) A := (jump_itr n A)′

theorem lt_jump (A : set ℕ) : A <ₜ A′ := 
⟨classical_iff.mpr
  begin
    show chr A computable_in! chr A′,
    have : ∃ e, ∀ x, (⟦e⟧ₙ^(chr A) x).dom ↔ A x,
    { have : ∃ e, ⟦e⟧ₙ^(chr A) = λ a, cond (chr A a) (some 0) none :=
        exists_index.mp (bool_to_roption (chr A)),
      rcases this with ⟨e, he⟩,
      refine ⟨e, λ x, _⟩,
      show (⟦e⟧ₙ^(chr A) x).dom ↔ A x,
      simp [he],
      cases e : chr A x,
      simp[(chr_ff_iff _ _).1 e], rintros ⟨f, _⟩, 
      simp[(chr_iff _ _).1 e] },
    rcases this with ⟨e, he⟩,
    let f := λ x, chr A′ (e.mkpair x),
    have lmm_f : f computable_in! chr A′ :=
        (rcomputable.refl.comp (primrec₂.mkpair.comp (primrec.const e) primrec.id).to_rcomp),
    have : f = chr A,
    { funext x, simp[f, jump, chr_ext, set.set_of_app_iff, he], },
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
      simp[(chr_iff _ _).1 e], rintros ⟨_, _⟩ },
    rcases this with ⟨e, he⟩,
    have : (e.mkpair e) ∉ A′ ↔ (e.mkpair e) ∈ A′,
    calc
      (e.mkpair e) ∉ A′ ↔ ¬(⟦e⟧ₙ^(chr A) e).dom : by simp[jump]
                    ... ↔ (e.mkpair e) ∈ A′     : by simp[he],
    show false, from (not_iff_self _).mp this
  end⟩

theorem le_le_jump {A B : set ℕ} : A ≤ₜ B → A′ ≤₁ B′ := λ h,
begin
  have h' := classical_iff.mp h,
  let f := (λ x : ℕ, ⟦x.unpair.1⟧ₙ^(chr A) x.unpair.2),
  have : ∃ e, ⟦e⟧ₙ^(chr B) = f,
  { have := (rpartrec.univ_tot ℕ ℕ (primrec.fst.comp primrec.unpair).to_rcomp h'
      (primrec.snd.comp primrec.unpair).to_rcomp), 
    exact exists_index.mp this },
  rcases this with ⟨e, lmm_e⟩,
  have iff : ∀ x, A′ x ↔ B′ (e.mkpair x),
  { simp [jump, lmm_e] },
  have pi : primrec e.mkpair := primrec₂.mkpair.comp (primrec.const e) (primrec.id),
  have inj : function.injective e.mkpair,
  { intros x y,  intros h,
    have : x = (e.mkpair x).unpair.2, simp,
    rw this, rw h, simp },  
  refine ⟨e.mkpair, pi.to_comp, inj, iff⟩,
end

open primrec

theorem Kleene_equiv_jump (A : set ℕ) : Kleene A ≡ₜ A′ :=
⟨classical_iff.mpr 
  begin
    show chr (Kleene A) computable_in! chr A′,
    let f := (λ n : ℕ, chr A′ (n.mkpair n)),
    have : chr (Kleene A) = f,
    { funext n, apply chr_ext.mpr,
      simp [Kleene, f, jump] },
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
      simp [Kleene, f, jump, eqn_k, eqn_e] },
    rw this,
    have : primrec₂ k := curry_prim.comp
      (curry_prim.comp (const e) fst) snd,
    have := rcomputable.refl.comp
      (this.comp (fst.comp primrec.unpair)
      (snd.comp primrec.unpair)).to_rcomp,
    exact this
  end⟩

lemma rre_pred_iff {p : set α} {f : β →. σ}:
  p re_in f ↔ ∃ q : ℕ →. ℕ, q partrec_in f ∧ (∀ x, p x ↔ (q $ encode x).dom) :=
begin
  split; assume h,
  { let q : ℕ →. ℕ := 
      λ n, roption.bind (decode α n) (λ a, roption.assert (p a) (λ (_ : p a), some 0)),
    have c : q partrec_in f :=
    (computable.decode.of_option.to_rpart).bind (h.comp rcomputable.snd),
    refine ⟨q, c, λ x, _⟩, 
    simp [q, roption.some, roption.assert, encodek] },
  { rcases h with ⟨q, pq, hq⟩,
    let g : α →. unit := (λ x, (q (encode x)).map (λ x, ())),
    have : g partrec_in f :=
      (pq.comp computable.encode.to_rpart).map (rcomputable.const ()),
    exact (this.of_eq $ λ x, by {
      simp[g], apply roption.ext, intros u, simp[hq, dom_iff_mem] }) }
end

lemma rre_pred.rre {f : α →. σ} {g : β →. τ} {A : set γ} :
  A re_in f → f partrec_in g → A re_in g :=
by simp [rre_pred_iff]; exact λ q pq h pf, ⟨q, pq.trans pf, h⟩

theorem t_reducible.rre {A : set α} {B : set β} :
  A ≤ₜ B → A re_in! chr B := λ h,
begin
  have : (λ a, cond (chr A a) (some ()) none) partrec_in! chr B,
  { refine rpartrec.cond (classical_iff.mp h) (rcomputable.const _) rpartrec.none },
  exact (this.of_eq $ λ a,
    by { apply roption.ext, simp, intros u, cases C : chr A a; simp at C ⊢; exact C })
end

theorem t_reducible.compl_rre {A : set α} {B : set β} :
  A ≤ₜ B → Aᶜ re_in! chr B := λ h,
begin
  have : (λ a, cond (chr A a) none (some ())) partrec_in! chr B,
  { refine rpartrec.cond (classical_iff.mp h) rpartrec.none (rcomputable.const _) },
  exact (this.of_eq $ λ a, by {
    apply roption.ext, simp, intros u, cases C : chr A a; simp at C ⊢, exact C,
    exact not_not.mpr C })
end

theorem rre_jumpcomputable {A : set α} {B : set ℕ} : A re_in! chr B → A ≤ₜ B′ := 
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
  { funext x, simp[f, jump, chr_ext, set.set_of_app_iff, he, ha], },
  show chr A computable_in! chr B′, from (l0.of_eq $ by simp[l1])
end

theorem rre_iff_one_one_reducible {A : set ℕ} {B : set ℕ} : A re_in! chr B ↔ A ≤₁ B′ := 
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
    { simp[jump, chr_ext, set.set_of_app_iff, eqn_e, ha], },  
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
    { intros x, simp [hi, q, jump] },
    refine ⟨q, lmm, lmm1⟩,
  end⟩

theorem re_many_one_reducible_to_0' {A : set ℕ} : r.e. A ↔ A ≤₁ ∅′ :=
⟨λ h, rre_iff_one_one_reducible.mp (h.to_rpart),
 λ h, (rre_iff_one_one_reducible.mpr h).re0 ⟩

lemma dom_rre (f : α →. σ) : {x | (f x).dom} re_in f :=
begin
  let g := (λ a, (f a).map (λ x, ())),
  have := rpartrec.refl.map ((computable.const ()).comp computable.snd).to_rcomp,
  exact (this.of_eq $ λ x, by { rw set.set_of_app_iff, simp, 
    apply roption.ext, intros a, simp [dom_iff_mem] })
end

theorem exists_rre [inhabited β] {p : α → β → Prop} {g : γ → τ} (h : prod.unpaired p re_in! g) :
  {x | ∃ y, p x y} re_in! g :=
begin
  have := rpartrec.exists_index.mp h,
  rcases this with ⟨e, eqn_e⟩,
  have eqn_e1 : ∀ x y, p x y ↔ (⟦e⟧^g (x, y) : roption unit).dom,
  { simp [eqn_e, roption.assert, roption.some] },
  let p' := (λ x : α, nat.rfind (λ u, (⟦e⟧^g [u.unpair.2]
    (x, (decode β u.unpair.1).get_or_else (default β)) : option unit).is_some)),
  have lmm : ∀ x, (∃ y, p x y) ↔ (p' x).dom,
  { intros x, simp only [p'], split,
    { rintros ⟨y, hb⟩, rw eqn_e1 at hb,
      apply rfind_dom_total,
      simp [roption.dom_iff_mem, roption.some] at hb ⊢, rcases hb with ⟨z, hz⟩,
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
  { apply rpartrec.rfind', simp,
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

theorem exists_reducible [inhabited β] {p : α → β → Prop} {A : set ℕ} :
  {x : α × β | p x.1 x.2} ≤ₜ A → {x | ∃ y, p x y} ≤ₜ A′ :=
λ h, rre_jumpcomputable (exists_rre h.rre)

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

lemma rre_enumeration_iff {A : set α} {f : β → σ} (h : ∃ a, a ∈ A) :
  A re_in! f → ∃ e : ℕ → α, e computable_in! f ∧ (∀ x, x ∈ A ↔ ∃ n, e n = x) :=
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
        have : ∃ y : ℕ, y ∈ (⟦i⟧^f a : roption ℕ),
        { simp [←roption.dom_iff_mem, eqn_i, q', ←hyp_q1], exact hyp_a },
        rcases this with ⟨y, lmm_y⟩,
        have := univn_complete.mp lmm_y, rcases this with ⟨s, lmm_s⟩,
        refine ⟨s.mkpair (encode a), _⟩, simp, simp[lmm_s] },
      { rintros ⟨n, hyp_n⟩,
        cases C : (⟦i⟧^f [n.unpair.fst] ((decode α n.unpair.snd).get_or_else a₀) : option ℕ) with v;
        simp[C] at hyp_n, simp[←hyp_n], exact hyp_a₀,
        suffices : (⟦i⟧^f a : roption ℕ).dom,
        { simp[eqn_i, q', ←hyp_q1] at this, exact this },
        have := univn_sound C,
        simp[←hyp_n, this] } },
    refine ⟨e, lmm1, lmm2⟩ }
end

lemma re_enumeration_iff {A : set α} {f : β → σ} (h : ∃ a, a ∈ A) :
  r.e. A → ∃ e : ℕ → α, computable e ∧ (∀ x, x ∈ A ↔ ∃ n, e n = x) := λ hyp,
by { rcases rre_enumeration_iff h (hyp.to_rpart_in ↑ᵣ(@id ℕ)) with ⟨e, lmm1, lmm2⟩,
     refine ⟨e, rcomputable.le_comp_comp lmm1 computable.id, lmm2⟩ }

end classical