import computability.primrec
import computability.partrec
import computability.partrec_code
import computability.halting
import data.pfun
import tactic
import code

open encodable denumerable roption

namespace nat

inductive rpartrec (o : ℕ →. ℕ) : (ℕ →. ℕ) → Prop
| oracle : rpartrec (λ x, o x)
| zero : rpartrec (pure 0)
| succ : rpartrec succ
| left : rpartrec ↑(λ n : ℕ, n.unpair.1)
| right : rpartrec ↑(λ n : ℕ, n.unpair.2)
| pair {f g} : rpartrec f → rpartrec g → rpartrec (λ n, mkpair <$> f n <*> g n)
| comp {f g} : rpartrec f → rpartrec g → rpartrec (λ n, g n >>= f)
| prec {f g} : rpartrec f → rpartrec g → rpartrec (unpaired (λ a n,
    n.elim (f a) (λ y IH, do i ← IH, g (mkpair a (mkpair y i)))))
| rfind {f} : rpartrec f → rpartrec (λ a, rfind (λ n, (λ m, m = 0) <$> f (mkpair a n)))
| univn {f : ℕ →. ℕ} [decidable_pred f.dom] : rpartrec f → rpartrec (unpaired $ λ a n, 
    nat.rpartrec.code.evaln_ropt a.unpair.1 f (of_nat _ a.unpair.2) n)

namespace rpartrec

def reducible (f g) : Prop := rpartrec g f
local infix ` partrec_in `:80 := reducible

theorem of_eq {o f g : ℕ →. ℕ} (hf : rpartrec o f) (H : ∀ n, f n = g n) : rpartrec o g :=
(funext H : f = g) ▸ hf

theorem of_partrec {f} (g) (hf : nat.partrec f) : f partrec_in g :=
begin
  induction hf,
  case nat.partrec.zero { exact zero },
  case nat.partrec.succ { exact succ },
  case nat.partrec.left { exact left },
  case nat.partrec.right { exact right },
  case nat.partrec.pair : f g hf hg pf pg { exact pair pf pg },
  case nat.partrec.comp : f g hf hg pf pg { exact comp pf pg },
  case nat.partrec.prec : f g hf hg pf pg { exact prec pf pg },
  case nat.partrec.rfind : f pf hf { exact rfind hf },
end

theorem of_primrec {f} (g) (hf : primrec f) : f partrec_in g := 
of_partrec g (partrec.of_primrec hf)

protected theorem some {f} : roption.some partrec_in f := of_primrec f primrec.id

theorem none {f} : (λ n, none) partrec_in f := of_partrec f partrec.none

theorem prec' {f g h o} (hf : f partrec_in o) (hg : g partrec_in o) (hh : h partrec_in o) :
  (λ a, (f a).bind (λ n, n.elim (g a) (λ y IH, do i ← IH, h (mkpair a (mkpair y i))))) partrec_in o :=
((prec hg hh).comp (pair rpartrec.some hf)).of_eq $ λ a, ext $ λ s, by simp [(<*>)]

theorem refl {f : ℕ →. ℕ} : f partrec_in f := oracle

theorem trans {f g h : ℕ →. ℕ} : f partrec_in g → g partrec_in h → f partrec_in h :=
begin
  assume pgf phg,
  induction pgf,
  case oracle { exact phg },
  case zero { exact zero },
  case succ { exact succ },
  case left { exact left },
  case right { exact right },
  case pair : _ _ _ _ pf pg { exact pair pf pg },
  case comp : _ _ _ _ pf pg { exact comp pf pg },
  case prec : _ _ _ _ pf pg { exact prec pf pg },
  case rfind : _ _ pf { exact rfind pf },
  case univn : _ _ _ pf { exactI univn pf },  
end

end rpartrec

end nat

def rpartrec {α β σ τ} [primcodable α] [primcodable β] [primcodable σ] [primcodable τ] 
  (f : α →. σ) (g : β →. τ) := nat.rpartrec.reducible
(λ n, roption.bind (decode α n) (λ a, (f a).map encode))
(λ n, roption.bind (decode β n) (λ a, (g a).map encode))
infix ` partrec_in `:80 := rpartrec

def rcomputable {α β σ τ} [primcodable α] [primcodable β] [primcodable σ] [primcodable τ]
  (f : α → σ) (g : β →. τ) := (f : α →. σ) partrec_in g
infix ` computable_in `:80 := rcomputable

theorem partrec.to_rpart {α σ β τ} [primcodable α] [primcodable σ] [primcodable β] [primcodable τ]
  {f : α →. σ} {g : β →. τ} (h : partrec f) : f partrec_in g := nat.rpartrec.of_partrec _ h

theorem partrec.to_rpart_in {α σ β τ} [primcodable α] [primcodable σ] [primcodable β] [primcodable τ]
  {f : α →. σ} (g : β →. τ) (h : partrec f) : f partrec_in g := nat.rpartrec.of_partrec _ h

theorem computable.to_rcomp {α σ β τ} [primcodable α] [primcodable σ] [primcodable β] [primcodable τ]
  {f : α → σ} {g : β →. τ} (h : computable f) : f computable_in g := nat.rpartrec.of_partrec _ h

theorem computable.to_rcomp_in {α σ β τ} [primcodable α] [primcodable σ] [primcodable β] [primcodable τ]
  {f : α → σ} (g : β →. τ) (h : computable f) : f computable_in g := nat.rpartrec.of_partrec _ h

namespace rpartrec
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem of_eq {f g : α →. σ} {h : β →. τ} (hf : f partrec_in h) (H : ∀ n, f n = g n) : g partrec_in h :=
(funext H : f = g) ▸ hf

theorem comp {f : β →. γ} {g : α → β} {h : σ →. τ} 
  (hf : f partrec_in h) (hg : (g : α →. β) partrec_in h) : (λ a, f (g a)) partrec_in h :=
(nat.rpartrec.comp hf hg).of_eq $ λ n, by simp; cases e : decode α n with a; simp [e, encodek]

theorem nat_elim {f : α → ℕ} {g : α →. σ} {h : α × ℕ × σ →. σ} {i : β →. γ}
  (hf : (f : α →. ℕ) partrec_in i) (hg : g partrec_in i) (hh : h partrec_in i) :
  (λ a, (f a).elim (g a) (λ y IH, IH.bind (λ i, h (a, y, i)))) partrec_in i :=
(nat.rpartrec.prec' hf hg hh).of_eq $ λ n, begin
  cases e : decode α n with a; simp [e],
  induction f a with m IH; simp,
  rw [IH, bind_map],
  congr, funext s,
  simp [encodek]
end

@[refl] theorem refl {f : α →. β} : f partrec_in f := nat.rpartrec.refl
theorem refl_in (f : α →. β) : f partrec_in f := nat.rpartrec.refl

@[trans] theorem trans {f : α →. σ} {g : β →. τ} {h : γ →. μ} : f partrec_in g → g partrec_in h → f partrec_in h :=
nat.rpartrec.trans

theorem nat_iff {f g} : f partrec_in g ↔ nat.rpartrec.reducible f g  :=
by simp[rpartrec, encodable.encode, map]

theorem bind {f : α →. β} {g : α × β →. σ} {h : γ →. τ}
  (hf : f partrec_in h) (hg : g partrec_in h) : (λ a, (f a).bind (λ x, g (a, x))) partrec_in h :=
(nat.rpartrec.comp hg (nat.rpartrec.some.pair hf)).of_eq $
λ n, by simp [(<*>)]; cases e : decode α n with a;
  simp [e, encodek]

theorem map {f : α →. β} {g : α × β → σ} {h : γ →. τ}
  (hf : f partrec_in h) (hg : (g : α × β →. σ) partrec_in h) : (λ a, (f a).map (λ x, g (a, x))) partrec_in h :=
by simpa [bind_some_eq_map] 
  using @rpartrec.bind _ _ _ _ _ _ _ _ _ _ _ (λ x, roption.some (g x)) _ hf hg

theorem rfind {p : α × ℕ →. bool} : (λ a, nat.rfind (λ x, p (a, x))) partrec_in p :=
  have c₀ : (λ x, (p x).map (λ b, cond b 0 1) : α × ℕ →. ℕ) partrec_in p :=
    rpartrec.refl.map ((
      (primrec.dom_bool (λ b, cond b 0 1)).comp primrec.snd).to_comp.to_rpart),
((nat.rpartrec.rfind c₀).of_eq $ λ n, by 
{ cases e : decode α n with a;
  simp [e, nat.rfind_zero_none, map_id'],
  congr, funext n,
  simp [roption.map_map, (∘)],
  apply map_id' (λ b, _),
  cases b; refl })

end rpartrec

namespace rcomputable

variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ] [primcodable τ] [primcodable μ]

theorem of_eq {f g : α → σ} {h : β →. τ} (hf : f computable_in h) (H : ∀ n, f n = g n) :
  g computable_in h := (funext H : f = g) ▸ hf

theorem comp {f : β → γ} {g : α → β} {h : σ →. τ} 
  (hf : f computable_in h) (hg : g computable_in h) : (λ a, f (g a)) computable_in h :=
(nat.rpartrec.comp hf hg).of_eq $ λ n, by simp; cases e : decode α n with a; simp [e, encodek]

theorem nat_elim
  {f : α → ℕ} {g : α → σ} {h : α × ℕ × σ → σ} {o : β →. γ}
  (hf : f computable_in o) (hg : g computable_in o) (hh : h computable_in o) :
  (λ a, (f a).elim (g a) (λ y IH, h (a, y, IH))) computable_in o :=
((rpartrec.nat_elim hf hg hh).of_eq) $
λ a, by { unfold_coes, simp, induction f a with m, simp, simp[ih] }

theorem id {f : β →. σ} : (@id α) computable_in f := computable.id.to_rcomp

theorem fst {f : γ →. σ} : (@prod.fst α β) computable_in f := computable.fst.to_rcomp

theorem snd {f : γ →. σ} : (@prod.snd α β) computable_in f := computable.snd.to_rcomp

theorem pair {f : α → σ} {g : α → τ} {h : γ →. μ}
  (hf : f computable_in h) (hg : g computable_in h) : (λ x, (f x, g x)) computable_in h
:= (nat.rpartrec.pair hf hg).of_eq $ λ n, by cases decode α n; simp [(<*>)]

theorem const (a : α) {f : γ →. σ} : (λ x, a : β → α) computable_in f :=
(computable.const a).to_rcomp

protected theorem encode {f : β →. σ} : (@encode α _) computable_in f := computable.encode.to_rcomp

protected theorem decode {f : β →. σ} : (@decode α _) computable_in f := computable.decode.to_rcomp

@[refl] theorem refl {f : α → β} : f computable_in (f : α →. β) := nat.rpartrec.refl
theorem refl_in (f : α → β) : f computable_in (f : α →. β) := nat.rpartrec.refl

@[trans] theorem trans {f : α → σ} {g : β → τ} {h : γ →. μ} :
  f computable_in (g : β →. τ)→ g computable_in h → f computable_in h := nat.rpartrec.trans

end rcomputable

namespace nat.rpartrec.code
open nat.rpartrec (code)

@[simp] lemma eval_eval_opt {α β} (f : α →. β) [D : decidable_pred f.dom] {x} :
  f.eval_opt x = @roption.to_option _ (f x) (D x) := rfl

lemma eq_none_or_eq_some_dec {α} (o : roption α) [decidable o.dom] : o = none ∨ ∃ x, o = some x :=
by { exact eq_none_or_eq_some o }

private lemma evaln_comp_dec {c f} [D : decidable_pred (eval f c).dom] : ∀ m, ∃ s₀,
  ∀ n a, n < m → eval f c n = some a → evaln s₀ f c n = some a := λ m,
begin
  induction m with m0 ih, simp,
  rcases ih with ⟨s₀, hs₀⟩,
  have e : eval f c m0 = none ∨ ∃ v, eval f c m0 = some v := eq_none_or_eq_some (eval f c m0),
  cases e,
  { refine ⟨s₀, λ n a en ha, _⟩,
    have : n < m0 ∨ n = m0, from nat.lt_succ_iff_lt_or_eq.mp en,
    cases this, { exact hs₀ _ _ this ha },
    { exfalso, rw this at ha, rw e at ha, exact roption.some_ne_none _ (eq.symm ha) } },
  { rcases e with ⟨v, e⟩,
    have : v ∈ eval f c m0, simp[e],
    have : ∃ k, v ∈ evaln k f c m0 := evaln_complete.mp this, rcases this with ⟨s₁, hs₁⟩,
    refine ⟨max s₀ s₁, _⟩,
    intros n a en ha,
    have en' : n < m0 ∨ n = m0, from nat.lt_succ_iff_lt_or_eq.mp en,
    cases en', 
    { have : evaln s₀ f c n = option.some a := hs₀ _ _ en' ha,
      show evaln (max s₀ s₁) f c n = option.some a,
        from evaln_mono (le_max_left s₀ s₁) this },
    { rw en', 
      have : a = v, from roption.some_inj.mp (by simp only [←e, ←ha, en']),
      show evaln (max s₀ s₁) f c m0 = option.some a, rw this,
        from evaln_mono (le_max_right s₀ s₁) hs₁ } }
end

@[simp] theorem mem_to_option' {α} {o : roption α} [decidable o.dom] {a : α} :
  to_option o = some a ↔ a ∈ o := mem_to_option

theorem eval_univn_eq_dec (c f) [D : decidable_pred (eval f c).dom] : 
  eval f c.univn = nat.unpaired (λ a n, (evaln a.unpair.fst (eval f c).eval_opt (of_nat code a.unpair.snd) n)) :=
begin
  funext n, apply roption.ext, intros a,
  rw eval_univn_evaln_iff, 
  simp[evaln_univn, (>>)], split,
  { rintros ⟨s, hs⟩, rcases hs with ⟨e, hs⟩,
    have : ∀ x y, evaln (s+1) f c x = some y → (eval f c).eval_opt x = some y,
    { intros x y ey, simp[eval_eval_opt], have := evaln_sound ey, exact this },    
    have := evaln_inclusion (λ x y e, this x y) _ _ hs,
    exact this },
  { assume ha, 
    have : ∃ s₀, ∀ m a, m < n.unpair.fst.unpair.fst →
      eval f c m = option.some a → evaln s₀ f c m = option.some a :=
    evaln_comp_dec n.unpair.1.unpair.1, rcases this with ⟨s₀, hs₀⟩,
    refine ⟨max n s₀, le_max_left _ _, _⟩, 
    have hs₀' : ∀ m a, m < n.unpair.fst.unpair.fst →
      (eval f c).eval_opt m = some a → evaln (max n s₀ + 1) f c m = option.some a,
    from λ _ _ em ha, evaln_mono (le_trans (le_max_right n _) (nat.le_succ _)) (hs₀ _ _ em (
      by { simp at ha, simp[of_option, roption.eq_some_iff] at ha ⊢, exact ha})),
    exact evaln_inclusion hs₀' _ _ ha } 
end

theorem rfind'' {f} : nat.rpartrec f (nat.unpaired (λ a m,
  (nat.rfind (λ n, (λ m, m = 0) <$> f (nat.mkpair a (n + m)))).map (+ m))) :=
rpartrec.nat_iff.mp $
begin
  simp,
  have c₀ : primrec (λ (x : (ℕ × ℕ) × ℕ), x.2 + x.1.2) := 
  primrec.nat_add.comp primrec.snd (primrec.snd.comp primrec.fst),
  have c₁ : primrec (λ (m : ((ℕ × ℕ) × ℕ) × ℕ), to_bool (m.2 = 0)) :=
  primrec₂.comp primrec.eq primrec.snd (primrec.const 0),
  have c₂ : (λ (x : (ℕ × ℕ) × ℕ), f (x.1.1.mkpair (x.2 + x.1.2))) partrec_in f :=
  rpartrec.refl.comp (primrec₂.mkpair.comp (primrec.fst.comp primrec.fst) $
    primrec.nat_add.comp primrec.snd (primrec.snd.comp primrec.fst)).to_comp.to_rpart,
  have := (rpartrec.rfind.trans (c₂.map c₁.to_comp.to_rcomp)).map c₀.to_comp.to_rcomp,
  simp at this,
  exact this.comp primrec.unpair.to_comp.to_rcomp
end
--
--theorem rpartrec.evaln {f : ℕ →. ℕ} [D : decidable_pred f.dom] :
--  nat.rpartrec f (nat.unpaired $ λ a n, 
--    nat.rpartrec.code.evaln_ropt a.unpair.1 f (of_nat _ a.unpair.2) n) := λ h,
--
theorem exists_code {f g : ℕ →. ℕ} [D : decidable_pred g.dom] :
  nat.rpartrec g f → ∃ c, eval (g.eval_opt) c = f := λ h,
begin
  induction h,
  case nat.rpartrec.oracle 
  { exact ⟨oracle, by { simp[eval], funext n, exact of_to_option (g n) }⟩ },  
  case nat.rpartrec.zero   { exact ⟨zero, rfl⟩ },
  case nat.rpartrec.succ   { exact ⟨succ, rfl⟩ },
  case nat.rpartrec.left   { exact ⟨left, rfl⟩ },
  case nat.rpartrec.right  { exact ⟨right, rfl⟩ },
  case nat.rpartrec.pair : f₀ f₁ pf₀ pf₁ hf₀ hf₁
  { rcases hf₀ with ⟨e₀, rfl⟩, rcases hf₁ with ⟨e₁, rfl⟩,
    exact ⟨pair e₀ e₁, rfl⟩ },
  case nat.rpartrec.comp : f₀ f₁ pf₀ pf₁ hf₀ hf₁
  { rcases hf₀ with ⟨e₀, rfl⟩, rcases hf₁ with ⟨e₁, rfl⟩,
    exact ⟨comp e₀ e₁, rfl⟩ },
  case nat.rpartrec.prec : f₀ f₁ pf₀ pf₁ hf₀ hf₁
  { rcases hf₀ with ⟨e₀, rfl⟩, rcases hf₁ with ⟨e₁, rfl⟩,
    exact ⟨prec e₀ e₁, rfl⟩ },
  case nat.rpartrec.rfind : f₀ pf₀ hf₀
  { rcases hf₀ with ⟨e₀, rfl⟩, 
    refine ⟨comp (rfind' e₀) (pair nat.rpartrec.code.id zero), _⟩,
    simp [eval, (<*>), pure, pfun.pure, roption.map_id'],  },
  case nat.rpartrec.univn : f₀ D pf₀ hf₀
  { rcases hf₀ with ⟨e₀, rfl⟩,
    have := by exactI eval_univn_eq_dec e₀ g.eval_opt,
    refine ⟨e₀.univn, this⟩ }
end

end nat.rpartrec.code