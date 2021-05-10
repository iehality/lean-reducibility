import coding computable_function partrec_eval
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

lemma encode_to_bool_eq {α} {A : α → Prop} (D0 D1 : decidable_pred A) :
  (λ n, (@to_bool (A n) (D0 n))) = (λ n, (@to_bool (A n) (D1 n))) := funext (λ x, by rw bool.to_bool_ext)

lemma decidable_pred.compl {α} {A : set α} :
  decidable_pred A → decidable_pred Aᶜ := λ h x, @not.decidable _ (h x)

noncomputable def chr {α} (p : α → Prop) : α → bool := λ x : α,
decidable.cases_on (classical.dec (p x)) (λ h₁, bool.ff) (λ h₂, bool.tt)

notation `chr* `A := λ x, some (chr A x)

@[simp] theorem chr_iff {α} (A : α → Prop) (x : α) : chr A x = tt ↔ A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

@[simp] theorem chr_ff_iff {α} (A : α → Prop) (x : α) : chr A x = ff ↔ ¬A x :=
by simp[chr]; cases (classical.dec (A x)); simp[h]

theorem to_bool_chr_eq {α} (A : α → Prop) (x : α) (D : decidable (A x)) :
  to_bool (A x) = chr A x :=
by { cases (@decidable.em (A x) D) with h,
     simp[to_bool_tt h, (chr_iff _ _).2 h],
     simp[to_bool_ff h, (chr_ff_iff _ _).2 h] }

theorem chr_ext {α β} {A : α → Prop} {B : β → Prop} {x y} : chr A x = chr B y ↔ (A x ↔ B y) :=
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
  (p : α → Prop) (f : β →. σ) : Prop :=
(λ a, roption.assert (p a) (λ _, roption.some ())) partrec_in f

@[simp] def rre_pred_s {α β} [primcodable β] [primcodable α]
  (p : α → Prop) (q : β → Prop) : Prop := rre_pred p (chr q : β →. bool)

infix ` re_in `:80 := rre_pred_s

def t_reducible {α β} [primcodable α] [primcodable β] (A : α → Prop) (B : β → Prop) : Prop := 
∃ [D0 : decidable_pred A] [D1 : decidable_pred B],
by exactI (λ x, to_bool (A x)) computable_in (λ x, to_bool (B x) : β →. bool) 

infix ` ≤ₜ `:25 := t_reducible

notation A` ≰ₜ `B:25 := ¬(A ≤ₜ B)

def t_reducible_lt {α β} [primcodable α] [primcodable β] (A : α → Prop) (B : β → Prop) : Prop :=
(A ≤ₜ B) ∧ ¬(B ≤ₜ A)

infix ` <ₜ `:25 := t_reducible_lt

def t_reducible_equiv {α β} [primcodable α] [primcodable β] (A : α → Prop) (B : β → Prop) : Prop :=
(A ≤ₜ B) ∧ (B ≤ₜ A)

infix ` ≡ₜ `:25 := t_reducible_equiv 

namespace t_reducible

open rpartrec rcomputable

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem classical_iff {A : α → Prop} {B : β → Prop} :
  A ≤ₜ B ↔ chr A computable_in (chr* B) :=
by simp[t_reducible, to_bool_chr_eq]; exact
  ⟨λ ⟨_, _, h⟩, h, λ h, ⟨classical.dec_pred _, classical.dec_pred _, h⟩⟩

theorem of_eq {A B : α → Prop} {C : β → Prop} (hA : A ≤ₜ C) (H : ∀ n, A n ↔ B n) : B ≤ₜ C :=
(set.ext H : A = B) ▸ hA

@[refl] theorem refl (A : α → Prop) [D : decidable_pred A] : A ≤ₜ A := ⟨D, D, nat.rpartrec.refl⟩

@[trans] theorem trans (A : α → Prop) (B : β → Prop) (C : γ → Prop)
  : A ≤ₜ B → B ≤ₜ C → A ≤ₜ C :=
λ ⟨Da, Db, hab⟩ ⟨Db0, Dc, hbc⟩, ⟨Da, Dc, by { simp only [encode_to_bool_eq Db Db0] at hab, exact nat.rpartrec.trans hab hbc }⟩

theorem reducible_compl (A : set α) [D : decidable_pred A] : Aᶜ ≤ₜ A :=
have Dc : decidable_pred Aᶜ, from D.compl,
have e0 : ∀ x, @to_bool (Aᶜ x) (Dc x) = !to_bool (A x), from λ x, bool.to_bool_ext_bnot _ _ _,
have cb : computable bnot, from (primrec.dom_bool _).to_comp,
⟨Dc, D, (cb.to_rpart.comp rcomputable.refl).of_eq $ λ x, by simp[e0]⟩

theorem equiv_compl (A : set ℕ) [D : decidable_pred A] : Aᶜ ≡ₜ A :=
have cc : Aᶜᶜ = A, from compl_compl A,
⟨reducible_compl A, by { 
  suffices : Aᶜᶜ ≤ₜ Aᶜ, rw cc at this, exact this, exact @reducible_compl _ _ Aᶜ D.compl, }⟩ 

theorem computable_le (A : α → Prop) (B : β → Prop) [D : decidable_pred B] :
  computable_pred A → A ≤ₜ B :=
λ ⟨D0, hA⟩, ⟨D0, D, nat.rpartrec.of_partrec _ hA⟩

theorem le_computable_computable (A : α → Prop) (B : β → Prop) :
  B ≤ₜ A → computable_pred A → computable_pred B := λ ⟨Db, Da, h⟩ ⟨Da0, hA⟩,
⟨Db, by { simp only [computable, partrec, encode_to_bool_eq Da0 Da] at hA,
          exact rpartrec.le_part_part h hA}⟩

theorem computable_equiv (A : α → Prop) (B : β → Prop) :
  computable_pred A → computable_pred B → A ≡ₜ B :=
λ ⟨Da, ca⟩ ⟨Db, cb⟩, ⟨@computable_le _ _ _ _ A B Db ⟨Da, ca⟩, @computable_le _ _ _ _ B A Da ⟨Db, cb⟩⟩

theorem computable_0 : computable_pred (∅ : set α) := 
⟨λ x, decidable.false, ((computable.const ff).of_eq $ λ x, rfl)⟩

theorem degree0 (A : α → Prop) :
  computable_pred A ↔ A ≡ₜ (∅ : set β) := 
⟨λ ⟨D, h⟩, ⟨computable_le _ _ ⟨D, h⟩, @computable_le _ _ _ _ _ _ D computable_0⟩,
 λ ⟨h, _⟩, le_computable_computable _ _ h computable_0⟩

section classical

open rpartrec

def jump (A : set ℕ) : set ℕ := {x | (⟦x.unpair.1⟧^(chr* A) x.unpair.2 : roption ℕ).dom}

notation A`′`:1200 := jump A

theorem lt_jump (A : set ℕ) : A <ₜ A′ := 
⟨classical_iff.mpr $ rpartrec_univ_iff_total.mpr 
  begin
    show ∃ e, ⟦e⟧^(chr* A′) = ↑(chr A),
    have : ∃ e, ∀ x, (⟦e⟧^(chr* A) x : roption ℕ).dom ↔ A x,
    { have : ∃ e, ⟦e⟧^(chr* A) = λ a, cond (chr A a) (some 0) none :=
        rpartrec_univ_iff.mp (bool_to_roption (chr A)),
      rcases this with ⟨e, he⟩,
      refine ⟨e, λ x, _⟩,
      show (⟦e⟧^(chr* A) x : roption ℕ).dom ↔ A x,
      simp [he],
      cases e : chr A x,
      simp[(chr_ff_iff _ _).1 e], rintros ⟨f, _⟩, 
      simp[(chr_iff _ _).1 e] },
    rcases this with ⟨e, he⟩,
    let f := λ x, chr A′ (e.mkpair x),
    have : ∃ i, ⟦i⟧^(chr* A′) = (f : ℕ →. bool) :=
      rpartrec_univ_iff.mp 
        ((rcomputable.refl_in (chr A′)).comp $ (rcomputable.const e).pair rcomputable.id),
    rcases this with ⟨i, hi⟩,
    have : f = chr A,
    { funext x, simp[f, jump, chr_ext, set.set_of_app_iff, he] },
    show ∃ i, ⟦i⟧^(chr* A′) = ↑(chr A), from ⟨i, by simp[hi, this]⟩
  end,
  λ h : A′ ≤ₜ A,
  begin
    have l0 : ↑(chr A′) partrec_in ↑(chr A) := classical_iff.mp h,
    have : ∃ e, ∀ x : ℕ, (⟦e⟧^(chr* A) x : roption ℕ).dom ↔ (x.mkpair x) ∉ A′,
    { let f : ℕ →. ℕ := (λ a, cond (chr A′ (a.mkpair a)) none (some 0)),
      have : f partrec_in ↑(chr A) := 
        ((rpartrec.cond (rpartrec.refl_in $ (chr A′ : ℕ →. bool))
        partrec.none.to_rpart (const 0)).comp
          (primrec₂.mkpair.comp primrec.id primrec.id).to_comp.to_rcomp).trans l0,
      have : ∃ e, ⟦e⟧^(chr* A) = f := rpartrec_univ_iff.mp this,
      rcases this with ⟨e, he⟩,
      refine ⟨e, λ x, _⟩,
      simp[he, set.mem_def, f],
      cases e : chr A′ (x.mkpair x),
      simp[(chr_ff_iff _ _).1 e],
      simp[(chr_iff _ _).1 e], rintros ⟨_, _⟩ },
    rcases this with ⟨e, he⟩,
    have : (e.mkpair e) ∉ A′ ↔ (e.mkpair e) ∈ A′,
    calc
      (e.mkpair e) ∉ A′ ↔ ¬(⟦e⟧^(chr* A) e : roption ℕ).dom : by simp[jump]
                    ... ↔ (e.mkpair e) ∈ A′                : by simp[he],
    show false, from (not_iff_self _).mp this
  end⟩

lemma rre_pred_iff {p : α → Prop} {f : β →. σ}:
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

theorem rre_tred {A : set α} {B : set ℕ} : A re_in B → A ≤ₜ B′ := 
λ h, classical_iff.mpr 
begin
  rcases rre_pred_iff.mp h with ⟨a, pa, ha⟩,
  rcases rpartrec_univ_iff_total.mp pa with ⟨e, he⟩,
  let f : α → bool := (λ x, chr B′ (e.mkpair (encode x))),
  have l0 : f computable_in (chr B′ : ℕ →. bool) :=
    rcomputable.refl.comp (primrec₂.mkpair.comp
      (primrec.const e) primrec.encode).to_comp.to_rcomp,
  have l1 : f = chr A,
  { funext x, simp[f, jump, chr_ext, set.set_of_app_iff, he, ha] },
  show chr A computable_in ↑(chr B′), from (l0.of_eq $ by simp[l1])
end

theorem re_le_0prime {A : set α} : re_pred A → A ≤ₜ ∅′ := 
λ h, rre_tred (show A re_in (∅ : set ℕ), from h.to_rpart)

theorem partrec_dom_0prime {f : α →. σ} (pf : partrec f) :
  {x | (f x).dom} ≤ₜ ∅′ := 
re_le_0prime
begin
  simp [re_pred],
  let g := (λ a, (f a).map (λ x, ())),
  have := pf.map ((computable.const ()).comp computable.snd).to₂,
  exact (this.of_eq $ λ x, by { rw set.set_of_app_iff, simp, 
    apply roption.ext, intros a, simp [dom_iff_mem] })
end
#check ε_operator

open nat.partrec

theorem partrec_dom_exists_0prime [inhabited β] {f : α → β →. σ} (pf : partrec₂ f) :
  {x | ∃ y, (f x y).dom} ≤ₜ ∅′ := 
let ⟨e, hf⟩ := exists_index.1 pf in
begin
  have : ∀ x, (∃ y, (f x y).dom) ↔ (nat.rfind (λ u, 
  (⟦e⟧₀ [u.unpair.2] (x, (decode β u.unpair.1).get_or_else (default β)) : option σ).is_some)).dom,
  { intros x, split; simp [roption.some],
    { intros b hb,  } }
end

end classical

end t_reducible
