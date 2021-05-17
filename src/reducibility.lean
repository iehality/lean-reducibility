import coding computable_function
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

notation `chr* `A := (λ x, option.some (chr A x))
notation `chr. `A := pfun.lift (chr A)

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

def rre_pred {β σ α} [primcodable β] [primcodable σ] [primcodable α]
  (p : set α) (f : β →. σ) : Prop :=
(λ a, roption.assert (p a) (λ _, roption.some ())) partrec_in f

infix ` re_in `:80 := rre_pred

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

--namespace t_reducible

--open rpartrec rcomputable

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem classical_iff {A : set α} {B : set β} :
  A ≤ₜ B ↔ chr A computable_in (chr. B) :=
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

theorem computable_le (A : set α) (B : set β) [D : decidable_pred B] :
  computable_pred A → A ≤ₜ B :=
λ ⟨D0, hA⟩, ⟨D0, D, nat.rpartrec.of_partrec _ hA⟩

theorem le_computable_computable (A : set α) (B : set β) :
  B ≤ₜ A → computable_pred A → computable_pred B := λ ⟨Db, Da, h⟩ ⟨Da0, hA⟩,
⟨Db, by { simp only [computable, partrec, encode_to_bool_eq Da0 Da] at hA,
          exact rpartrec.le_part_part h hA}⟩

theorem computable_equiv (A : set α) (B : set β) :
  computable_pred A → computable_pred B → A ≡ₜ B :=
λ ⟨Da, ca⟩ ⟨Db, cb⟩, ⟨@computable_le _ _ _ _ A B Db ⟨Da, ca⟩, @computable_le _ _ _ _ B A Da ⟨Db, cb⟩⟩

theorem computable_0 : computable_pred (∅ : set α) := 
⟨λ x, decidable.false, ((computable.const ff).of_eq $ λ x, rfl)⟩

theorem degree0 (A : set α) :
  computable_pred A ↔ A ≡ₜ (∅ : set β) := 
⟨λ ⟨D, h⟩, ⟨computable_le _ _ ⟨D, h⟩, @computable_le _ _ _ _ _ _ D computable_0⟩,
 λ ⟨h, _⟩, le_computable_computable _ _ h computable_0⟩

section classical
local attribute [instance, priority 0] classical.prop_decidable
open rpartrec

notation `⟦`e`⟧ᵪ^`f:max` [`s`]` := univn ℕ bool s f e
notation `⟦`e`⟧ᵪ^`f:max := univ ℕ bool f e
notation `⟦`e`⟧ₙ^`f:max` [`s`]` := univn ℕ ℕ s f e
notation `⟦`e`⟧ₙ^`f:max := univ ℕ ℕ f e

theorem cond_if_eq {α β} (p : set α) (x) (a b : β) :
  cond (chr p x) a b = if p x then a else b :=
by {by_cases h : p x; simp [h], simp [(chr_iff p x).mpr h], simp [(chr_ff_iff p x).mpr h] }

def jump (A : set ℕ) : set ℕ := {x | (⟦x.unpair.1⟧ₙ^(chr* A) x.unpair.2).dom}

notation A`′`:1200 := jump A

theorem lt_jump (A : set ℕ) : A <ₜ A′ := 
⟨classical_iff.mpr
  begin
    show chr A computable_in chr. A′,
    have : ∃ e, ∀ x, (⟦e⟧ₙ^(chr* A) x).dom ↔ A x,
    { have : ∃ e, ⟦e⟧ₙ^(chr* A) = λ a, cond (chr A a) (some 0) none :=
        rpartrec_univ_iff.mp (bool_to_roption (chr A)),
      rcases this with ⟨e, he⟩,
      refine ⟨e, λ x, _⟩,
      show (⟦e⟧ₙ^(chr* A) x).dom ↔ A x,
      simp [he],
      cases e : chr A x,
      simp[(chr_ff_iff _ _).1 e], rintros ⟨f, _⟩, 
      simp[(chr_iff _ _).1 e] },
    rcases this with ⟨e, he⟩,
    let f := λ x, chr A′ (e.mkpair x),
    have lmm_f : f computable_in chr* A′ :=
        (rcomputable.refl.comp (primrec₂.mkpair.comp (primrec.const e) primrec.id).to_comp.to_rcomp),
    have : f = chr A,
    { funext x, simp[f, jump, chr_ext, set.set_of_app_iff, he], },
    simp [←this], exact lmm_f,
  end,
  λ h : A′ ≤ₜ A,
  begin
    have l0 : chr A′ computable_in chr. A := classical_iff.mp h,
    have : ∃ e, ∀ x : ℕ, (⟦e⟧ₙ^(chr* A) x).dom ↔ (x.mkpair x) ∉ A′,
    { let f : ℕ →. ℕ := (λ a, cond (chr A′ (a.mkpair a)) none (some 0)),
      have : f partrec_in chr. A := 
        ((rpartrec.cond (rpartrec.refl_in $ (chr A′ : ℕ →. bool))
        partrec.none.to_rpart (rcomputable.const 0)).comp
          (primrec₂.mkpair.comp primrec.id primrec.id).to_comp.to_rcomp).trans l0,
      have : ∃ e, ⟦e⟧ₙ^(chr* A) = f := rpartrec_univ_iff_total.mp this,
      rcases this with ⟨e, he⟩,
      refine ⟨e, λ x, _⟩,
      simp[he, set.mem_def, f],
      cases e : chr A′ (x.mkpair x),
      simp[(chr_ff_iff _ _).1 e],
      simp[(chr_iff _ _).1 e], rintros ⟨_, _⟩ },
    rcases this with ⟨e, he⟩,
    have : (e.mkpair e) ∉ A′ ↔ (e.mkpair e) ∈ A′,
    calc
      (e.mkpair e) ∉ A′ ↔ ¬(⟦e⟧ₙ^(chr* A) e).dom : by simp[jump]
                    ... ↔ (e.mkpair e) ∈ A′      : by simp[he],
    show false, from (not_iff_self _).mp this
  end⟩

theorem le_le_jump {A B : set ℕ} : A ≤ₜ B → A′ ≤ₜ B′ := λ h,
classical_iff.mpr
begin
  have h' := classical_iff.mp h,
  let f := (λ x : ℕ, ⟦x.unpair.1⟧ₙ^(chr* A) x.unpair.2),
  have : ∃ e, ⟦e⟧ₙ^(chr* B) = f,
  { have := ((univ_rpartrec ℕ ℕ (chr* A)).comp
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

lemma dom_rre {f : α →. σ} {g : β →. τ} (hf : f partrec_in g) :
  {x | (f x).dom} re_in g :=
begin
  let g := (λ a, (f a).map (λ x, ())),
  have := hf.map ((computable.const ()).comp computable.snd).to_rcomp,
  exact (this.of_eq $ λ x, by { rw set.set_of_app_iff, simp, 
    apply roption.ext, intros a, simp [dom_iff_mem] })
end

theorem rre_jumpcomputable {A : set α} {B : set ℕ} : A re_in (chr. B) → A ≤ₜ B′ := 
λ h, classical_iff.mpr 
begin
  show chr A computable_in chr. B′,
  rcases rre_pred_iff.mp h with ⟨a, pa, ha⟩,
  rcases rpartrec_univ_iff_total.mp pa with ⟨e, he⟩,
  let f : α → bool := (λ x, chr B′ (e.mkpair (encode x))),
  have l0 : f computable_in (chr B′ : ℕ →. bool) :=
    rcomputable.refl.comp (primrec₂.mkpair.comp
      (primrec.const e) primrec.encode).to_comp.to_rcomp,
  have l1 : f = chr A,
  { funext x, simp[f, jump, chr_ext, set.set_of_app_iff, he, ha] },
  show chr A computable_in chr. B′, from (l0.of_eq $ by simp[l1])
end

theorem re_0'computable {A : set α} : re_pred A → A ≤ₜ (∅′ : set ℕ) := 
λ h, rre_jumpcomputable (show A re_in chr. (∅ : set ℕ), from h.to_rpart)

theorem dom_jumpcomputable {f : α →. σ} {A : set ℕ} (h : f partrec_in chr. A) :
  {x | (f x).dom} ≤ₜ A′ := 
rre_jumpcomputable (dom_rre h)

theorem dom_0'computable {f : α →. σ} (pf : partrec f) :
  {x | (f x).dom} ≤ₜ (∅′ : set ℕ) := 
dom_jumpcomputable pf.to_rpart

theorem rfind_dom_total {p : ℕ → bool} :
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

open primrec

theorem domex_jumpcomputable [inhabited β]
  {f : α × β →. σ} {A : set ℕ} (pf : f partrec_in chr. A) :
  {x | ∃ y, (f (x, y)).dom} ≤ₜ A′ := 
begin
  have := rpartrec.rpartrec_univ_iff_total.mp pf,
  rcases this with ⟨e, hf⟩,
  let p := (λ x : α, nat.rfind (λ u, (⟦e⟧^(chr* A) [u.unpair.2]
      (x, (decode β u.unpair.1).get_or_else (default β)) : option σ).is_some)),
  have lmm : ∀ x : α, (∃ y : β, (f (x, y) : roption σ).dom) ↔ (p x).dom,
  { intros x, simp only [p], rw ← hf, split, -- simp only[roption.dom_iff_mem, roption.some],
    { rintros ⟨y, hb⟩, 
      apply rfind_dom_total,
      simp [roption.dom_iff_mem, roption.some] at hb ⊢, rcases hb with ⟨z, hz⟩,
      rcases evaln_complete.mp hz with ⟨s, hs⟩,
      use (encode y).mkpair s,
      simp [hs], },
    { simp, intros u h0 h1, 
      use (decode β u.unpair.fst).get_or_else (default β),
      cases e : (⟦e⟧^(chr* A) [u.unpair.snd] (x, 
        (decode β u.unpair.fst).get_or_else (default β)) : option σ) with v,
      { exfalso, simp [e] at h0, exact h0 },
      have := evaln_sound e, simp [this] } },
  have eqn : {x | ∃ y, (f (x, y)).dom} = {x | (p x).dom},
  { apply set.ext, simp [lmm] },
  have : p partrec_in chr. A,
  { have c₀ := primrec.option_is_some.to_comp.to_rcomp.comp
      (univn_rcomputable (α × β) σ (chr* A)),
    have c₁ := (snd.comp $ unpair.comp $ snd).pair
      ((const e).pair (fst.pair (option_get_or_else.comp 
      (primrec.decode.comp $ fst.comp $ unpair.comp snd)
      (const (default β))))),
    have := c₀.comp c₁.to_comp.to_rcomp,
    have := rpartrec.rfind.trans this,
    exact this },
  rw eqn, exact dom_jumpcomputable this
end

theorem domex_0'computable [inhabited β] {f : α → β →. σ} 
  (pf : partrec₂ f) : {x | ∃ y, (f x y).dom} ≤ₜ (∅′ : set ℕ) :=
domex_jumpcomputable pf.to_rpart

theorem domex_jumpcomputable_f [inhabited γ] {f : α × β × γ →. σ} {g : α → β} {A : set ℕ}
  (pf : f partrec_in chr. A) (pg : g computable_in chr. A) :
  (λ x, chr {y | ∃ z, (f (x, y, z)).dom} (g x)) computable_in chr. A′ := 
begin
  have : (λ x, chr {y | ∃ z, (f (x, y, z)).dom} (g x)) =
    chr {x : α | ∃ z, (f (x, (g x), z)).dom},
  { funext n, apply chr_ext.mpr, simp },
  have := pf.comp (rcomputable.fst.pair 
    ((pg.comp rcomputable.fst).pair rcomputable.snd)),
  exact classical_iff.mp (domex_jumpcomputable this)
end

theorem domex_0'computable_f [inhabited γ] {f : α × β × γ →. σ} {g : α → β} {A : set ℕ}
  (pf : partrec f) (pg : computable g) :
  (λ x, chr {y | ∃ z, (f (x, y, z)).dom} (g x)) computable_in chr. (∅′ : set ℕ) :=
domex_jumpcomputable_f (pf.to_rpart_in chr. (∅ : set ℕ))
(pg.to_rpart_in chr. (∅ : set ℕ))

@[refl] theorem t_reducible_equiv.refl {α} [primcodable α] (A : set α) [D : decidable_pred A] :
  A ≡ₜ A :=
⟨t_reducible.refl A, t_reducible.refl A⟩

@[symm] theorem t_reducible_equiv.symm {A : set α} {B : set β} :
  A ≡ₜ B → B ≡ₜ A :=
and.swap

@[trans] theorem t_reducible_equiv.trans {A : set α} {B : set β} {C : set γ} :
  A ≡ₜ B → B ≡ₜ C → A ≡ₜ C :=
λ ⟨ab, ba⟩ ⟨bc, cb⟩, ⟨t_reducible.trans ab bc, t_reducible.trans cb ba⟩

theorem equivalence_of_t_reducible_equiv (α) [primcodable α] :
  equivalence (@t_reducible_equiv α α _ _) :=
⟨λ x, t_reducible_equiv.refl x, λ x y, t_reducible_equiv.symm, λ x y z, t_reducible_equiv.trans⟩

def turing_degree : Type :=
quotient (⟨t_reducible_equiv, equivalence_of_t_reducible_equiv ℕ⟩ : setoid (set ℕ))

namespace turing_degree

def of (A : set ℕ) : turing_degree := quotient.mk' A

@[elab_as_eliminator]
protected lemma ind_on {C : turing_degree → Prop} (d : turing_degree)
  (h : ∀ p : set ℕ, C (of p)) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : turing_degree) (f : set ℕ → φ)
  (h : ∀ p q, p ≡ₜ q → f p = f q) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (p : set ℕ) (f : set ℕ → φ)
  (h : ∀ p q, t_reducible_equiv p q → f p = f q) : (of p).lift_on f h = f p :=
rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : turing_degree) (f : set ℕ → set ℕ → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ≡ₜ q₁ → p₂ ≡ₜ q₂ → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (p q : set ℕ) (f : set ℕ → set ℕ → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ≡ₜ q₁ → p₂ ≡ₜ q₂ → f p₁ p₂ = f q₁ q₂) :
  (of p).lift_on₂ (of q) f h = f p q := rfl

@[simp] lemma of_eq_of {p q} : of p = of q ↔ p ≡ₜ q :=
by simp [of, quotient.eq']



instance : has_le turing_degree :=
⟨λ d₁ d₂, turing_degree.lift_on₂ d₁ d₂ (≤ₜ) $
  λ p₁ p₂ q₁ q₂ hp hq, propext ⟨λ hpq, (hp.2.trans hpq).trans hq.1, λ hpq, (hp.1.trans hpq).trans hq.2⟩⟩

instance : has_lt turing_degree := ⟨λ d₀ d₁, d₀ ≤ d₁ ∧ ¬ d₁ ≤ d₀⟩

instance : has_zero turing_degree := ⟨of (∅ : set ℕ)⟩

instance : inhabited turing_degree := ⟨0⟩

def djump : turing_degree → turing_degree :=
λ d, turing_degree.lift_on d (λ d, of d′)
(λ A B ⟨ab, ba⟩, by { simp, exact ⟨le_le_jump ab, le_le_jump ba⟩ })

notation d`⁺`:1200 := djump d

@[simp] lemma of_le_of {p q} : of p ≤ of q ↔ p ≤ₜ q := by refl

@[simp] lemma of_lt_of {p q} : of p < of q ↔ p <ₜ q := by refl

@[simp] lemma of_jump {A} : (of A)⁺ = of A′ := by refl

def Rec := {d | ∃ R : set ℕ, re_pred R ∧ d = of R}

notation `𝓡` := Rec

def High := {d | d ∈ 𝓡 ∧ d⁺ = 0⁺⁺}

def Low  := {d | d ∈ 𝓡 ∧ d⁺ = 0⁺}

end turing_degree

end classical