import coding function
open encodable denumerable roption

local attribute [simp] set.set_of_app_iff
#check computable.list_nth

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

--notation `chr* `A := (λ x, option.some (chr A x))
--notation `chr. `A := pfun.lift (chr A)

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

def rre_pred_tot {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  (p : set α) (f : β → σ) : Prop := p re_in ↑ᵣf

infix ` re_in! `:80 := rre_pred_tot

theorem rre_pred.re {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  {A : set α} {f : β →. σ} (hA : A re_in f) (hf : partrec f) : re_pred A :=
hA.le_part_part hf

def t_reducible {α β} [primcodable α] [primcodable β] (A : set α) (B : set β) : Prop := 
∃ [D0 : decidable_pred A] [D1 : decidable_pred B],
by exactI (λ x, to_bool (A x)) computable_in (λ x, to_bool (B x) : β →. bool) 

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

def creative (A : set ℕ) : Prop :=
re_pred A ∧ productive Aᶜ

def immune (A : set ℕ) : Prop := infinite A ∧ ∀ e, infinite W⟦e⟧ₙ⁰ → W⟦e⟧ₙ⁰ ∩ Aᶜ ≠ ∅

def simple (A : set ℕ) : Prop := re_pred A ∧ immune Aᶜ 

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem classical_iff {A : set α} {B : set β} :
  A ≤ₜ B ↔ chr A computable_in! (chr B) :=
by simp[t_reducible, to_bool_chr_eq]; exact
  ⟨λ ⟨_, _, h⟩, h, λ h, ⟨classical.dec_pred _, classical.dec_pred _, h⟩⟩

theorem of_eq {A B : set α} {C : set β} (hA : A ≤ₜ C) (H : ∀ n, A n ↔ B n) : B ≤ₜ C :=
(set.ext H : A = B) ▸ hA

@[refl] theorem t_reducible.refl (A : set α) [D : decidable_pred A] : A ≤ₜ A := ⟨D, D, nat.rpartrec.refl⟩

@[trans] theorem t_reducible.trans {A : set α} {B : set β} {C : set γ}
  : A ≤ₜ B → B ≤ₜ C → A ≤ₜ C :=
λ ⟨Da, Db, hab⟩ ⟨Db0, Dc, hbc⟩,
⟨Da, Dc, by simp only [encode_to_bool_eq Db Db0] at hab; exact nat.rpartrec.trans hab hbc⟩

theorem reducible_compl (A : set α) [D : decidable_pred A] : Aᶜ ≤ₜ A :=
have Dc : decidable_pred Aᶜ, from D.compl,
have e0 : ∀ x, @to_bool (Aᶜ x) (Dc x) = !to_bool (A x), from λ x, bool.to_bool_ext_bnot _ _ _,
have cb : computable bnot, from (primrec.dom_bool _).to_comp,
⟨Dc, D, (cb.to_rpart.comp rcomputable.refl).of_eq $ λ x, by simp[e0]⟩

theorem equiv_compl (A : set ℕ) [D : decidable_pred A] : Aᶜ ≡ₜ A :=
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

section classical
local attribute [instance, priority 0] classical.prop_decidable
open rpartrec

theorem cond_if_eq {α β} (p : set α) (x) (a b : β) :
  cond (chr p x) a b = if p x then a else b :=
by {by_cases h : p x; simp [h], simp [(chr_iff p x).mpr h], simp [(chr_ff_iff p x).mpr h] }

def jump (A : set ℕ) : set ℕ := {x | (⟦x.unpair.1⟧ₙ^(chr A) x.unpair.2).dom}
def kleene (A : set ℕ) : set ℕ := {x | (⟦x⟧ₙ^(chr A) x).dom}

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
        rpartrec_univ_iff.mp (bool_to_roption (chr A)),
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
        (rcomputable.refl.comp (primrec₂.mkpair.comp (primrec.const e) primrec.id).to_comp.to_rcomp),
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
          (primrec₂.mkpair.comp primrec.id primrec.id).to_comp.to_rcomp).trans l0,
      have : ∃ e, ⟦e⟧ₙ^(chr A) = f := rpartrec_univ_iff_total.mp this,
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
                    ... ↔ (e.mkpair e) ∈ A′      : by simp[he],
    show false, from (not_iff_self _).mp this
  end⟩

theorem le_le_jump {A B : set ℕ} : A ≤ₜ B → A′ ≤ₜ B′ := λ h,
classical_iff.mpr
begin
  have h' := classical_iff.mp h,
  let f := (λ x : ℕ, ⟦x.unpair.1⟧ₙ^(chr A) x.unpair.2),
  have : ∃ e, ⟦e⟧ₙ^(chr B) = f,
  { have := ((rpartrec.univ ℕ ℕ (chr A)).comp
      primrec.unpair.to_comp.to_rcomp).trans h', 
    exact rpartrec_univ_iff_total.mp this },
  rcases this with ⟨e, lmm_e⟩,
  have eqn : chr A′ = (λ x, chr B′ (e.mkpair x)),
  { funext x, apply chr_ext.mpr,
    show A′ x ↔ B′ (e.mkpair x), simp [jump, lmm_e] },
  rw eqn,
  exact (rcomputable.refl.comp
    (primrec₂.mkpair.comp (primrec.const e)
    primrec.id).to_comp.to_rcomp),
end

open primrec

theorem kleene_eq_jump (A : set ℕ) : kleene A ≡ₜ A′ :=
⟨classical_iff.mpr 
  begin
    show chr (kleene A) computable_in! chr A′,
    let f := (λ n : ℕ, chr A′ (n.mkpair n)),
    have : chr (kleene A) = f,
    { funext n, apply chr_ext.mpr,
      simp [kleene, f, jump] },
    rw this,
    have := rcomputable.refl.comp
      (primrec₂.mkpair.comp primrec.id primrec.id).to_comp.to_rcomp,
    exact this
  end, classical_iff.mpr
  begin
    show chr A′ computable_in! chr (kleene A),
    let t := (λ x : ℕ × (ℕ × ℕ), ⟦x.1⟧ₙ^(chr A) x.2.1),
    have : ∃ e, ⟦e⟧^(chr A) = t,
    { have : t partrec_in! chr A := (rpartrec.univ ℕ ℕ (chr A)).comp 
        (fst.pair (fst.comp snd)).to_comp.to_rcomp,
      exact rpartrec_univ_iff_total.mp this },
    rcases this with ⟨e, eqn_e⟩,
    let k := (λ n m : ℕ, curry (curry e n) m),
    have eqn_k : ∀ z i x, ⟦k i x⟧ₙ^(chr A) z = ⟦i⟧ₙ^(chr A) x,
    { intros z i x, simp [k, eqn_e] },
    let f := (λ x : ℕ, chr (kleene A) (k x.unpair.1 x.unpair.2)),
    have : chr A′ = f,
    { funext n, apply chr_ext.mpr,
      simp [kleene, f, jump, eqn_k, eqn_e] },
    rw this,
    have : primrec₂ k := curry_prim.comp
      (curry_prim.comp (const e) fst) snd,
    have := rcomputable.refl.comp
      (this.comp (fst.comp primrec.unpair)
      (snd.comp primrec.unpair)).to_comp.to_rcomp,
    exact this
  end⟩

lemma rre_pred_iff {p : set α} {f : β →. σ}:
  rre_pred p f ↔ ∃ q : ℕ →. ℕ, q partrec_in f ∧ (∀ x, p x ↔ (q $ encodable.encode x).dom) :=
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

lemma rre_pred.rre {f : α →. σ} {g : β →. τ} {A : set γ}
  : A re_in f → f partrec_in g → A re_in g :=
by simp [rre_pred_iff]; exact λ q pq h pf, ⟨q, pq.trans pf, h⟩

theorem rre_jumpcomputable {A : set α} {B : set ℕ} : A re_in! chr B → A ≤ₜ B′ := 
λ h, classical_iff.mpr 
begin
  show chr A computable_in! chr B′,
  rcases rre_pred_iff.mp h with ⟨a, pa, ha⟩,
  rcases rpartrec_univ_iff_total.mp pa with ⟨e, he⟩,
  let f : α → bool := (λ x, chr B′ (e.mkpair (encode x))),
  have l0 : f computable_in (chr B′ : ℕ →. bool) :=
    rcomputable.refl.comp (primrec₂.mkpair.comp
      (primrec.const e) primrec.encode).to_comp.to_rcomp,
  have l1 : f = chr A,
  { funext x, simp[f, jump, chr_ext, set.set_of_app_iff, he, ha], },
  show chr A computable_in! chr B′, from (l0.of_eq $ by simp[l1])
end

theorem re_0'computable {A : set α} : re_pred A → A ≤ₜ (∅′ : set ℕ) := 
λ h, rre_jumpcomputable (show A re_in! chr (∅ : set ℕ), from h.to_rpart)

lemma dom_rre (f : α →. σ) : {x | (f x).dom} re_in f :=
begin
  let g := (λ a, (f a).map (λ x, ())),
  have := rpartrec.refl.map ((computable.const ()).comp computable.snd).to_rcomp,
  exact (this.of_eq $ λ x, by { rw set.set_of_app_iff, simp, 
    apply roption.ext, intros a, simp [dom_iff_mem] })
end

private lemma rfind_dom_total {p : ℕ → bool} :
  (∃ n, p n = tt) → (nat.rfind p).dom :=
begin
  simp, intros n,
  induction n with n0 ih generalizing p,
  { assume h, use 0, simp [h] },
  { assume h, 
    let q := (λ n : ℕ, (p n.succ)),
    have q0 : q n0 = tt, simp[q], exact h,
    rcases ih q0 with ⟨m, qm, hm⟩, simp[q] at qm, simp[q] at hm,
    cases ep : p 0 with p0 p0,
    { use m.succ, split, exact qm,
      intros l el, simp [roption.some] },
    { use 0, exact ⟨eq.symm ep, by simp⟩ } }
end

theorem domex_rre [inhabited β] {f : α × β →. σ} {g : γ → τ}
  (h : f partrec_in! g) :
  {x | ∃ y, (f (x, y)).dom} re_in! g :=
begin
  let fo := (λ x, (f x).to_option),
  have pf : f partrec_in (λ x, fo x),
  { unfold_coes, simp [fo] },
  have pfo : (λ x, fo x) partrec_in f,
  { unfold_coes, simp [fo] },
  have := rpartrec.rpartrec_univ_iff_total.mp h,
  rcases this with ⟨e, hf⟩,
  let p := (λ x : α, nat.rfind (λ u, (⟦e⟧^g [u.unpair.2]
    (x, (decode β u.unpair.1).get_or_else (default β)) : option σ).is_some)),
  have lmm : ∀ x : α, (∃ y : β, (f (x, y) : roption σ).dom) ↔ (p x).dom,
  { intros x, simp only [p], rw ← hf, split,
    { rintros ⟨y, hb⟩, 
      apply rfind_dom_total,
      simp [roption.dom_iff_mem, roption.some] at hb ⊢, rcases hb with ⟨z, hz⟩,
      rcases evaln_complete.mp hz with ⟨s, hs⟩,
      use (encode y).mkpair s,
      simp [hs] },
    { simp, intros u h0 h1, 
      use (decode β u.unpair.fst).get_or_else (default β),
      cases e : (⟦e⟧^g [u.unpair.snd] (x, 
        (decode β u.unpair.fst).get_or_else (default β)) : option σ) with v,
      { exfalso, simp [e] at h0, exact h0 },
      have := evaln_sound e, simp [this] } },
  have eqn : {x | ∃ y, (f (x, y)).dom} = {x | (p x).dom},
  { apply set.ext, simp [lmm] },
  have : p partrec_in ↑ᵣg,
  { have c₀ := primrec.option_is_some.to_comp.to_rcomp.comp
      (rcomputable.univn (α × β) σ _),
    have c₁ := (snd.comp $ unpair.comp $ snd).pair
      ((const e).pair (fst.pair (option_get_or_else.comp 
      (primrec.decode.comp $ fst.comp $ unpair.comp snd)
      (const (default β))))),
    have := c₀.comp c₁.to_comp.to_rcomp,
    have := rpartrec.rfind.trans this,
    exact this },
  rw eqn,
  show {x : α | (p x).dom} re_in ↑ᵣg,
  from (dom_rre p).rre this,
end

theorem dom_jumpcomputable {f : α →. σ} {A : set ℕ} (h : f partrec_in! chr A) :
  {x | (f x).dom} ≤ₜ A′ := 
rre_jumpcomputable ((dom_rre f).rre h)

theorem dom_0'computable {f : α →. σ} (pf : partrec f) :
  {x | (f x).dom} ≤ₜ (∅′ : set ℕ) := 
dom_jumpcomputable pf.to_rpart

theorem domex_jumpcomputable [inhabited β]
  {f : α × β →. σ} {A} (pf : f partrec_in! chr A) :
  {x | ∃ y, (f (x, y)).dom} ≤ₜ A′ := 
rre_jumpcomputable (domex_rre pf)

theorem domex_0'computable [inhabited β] {f : α → β →. σ} 
  (pf : partrec₂ f) : {x | ∃ y, (f x y).dom} ≤ₜ (∅′ : set ℕ) :=
domex_jumpcomputable pf.to_rpart

end classical