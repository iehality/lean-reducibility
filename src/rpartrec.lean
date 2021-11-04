import computability.primrec
import computability.partrec
import computability.partrec_code
import computability.halting
import data.pfun
import tactic
import lib

open encodable denumerable part

namespace nat

inductive rpartrec (o : ℕ →. ℕ) : (ℕ →. ℕ) → Prop
| oracle : rpartrec o
| zero : rpartrec (pure 0)
| succ : rpartrec succ
| left : rpartrec ↑(λ n : ℕ, n.unpair.1)
| right : rpartrec ↑(λ n : ℕ, n.unpair.2)
| pair {f g} : rpartrec f → rpartrec g → rpartrec (λ n, mkpair <$> f n <*> g n)
| comp {f g} : rpartrec f → rpartrec g → rpartrec (λ n, g n >>= f)
| prec {f g} : rpartrec f → rpartrec g → rpartrec (unpaired (λ a n,
    n.elim (f a) (λ y IH, do i ← IH, g (mkpair a (mkpair y i)))))
| rfind {f} : rpartrec f → rpartrec (λ a, rfind (λ n, (λ m, m = 0) <$> f (mkpair a n)))

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

theorem le_part_part {f g : ℕ →. ℕ} : g partrec_in f → nat.partrec f → nat.partrec g :=
begin
  assume rgf pf,
  induction rgf,
  case oracle { exact pf },
  case zero { exact nat.partrec.zero },
  case succ { exact nat.partrec.succ },
  case left { exact nat.partrec.left },
  case right { exact nat.partrec.right },
  case pair : f g hf hg pf pg { exact nat.partrec.pair pf pg },
  case comp : f g hf hg pf pg { exact nat.partrec.comp pf pg },
  case prec : f g hf hg pf pg { exact nat.partrec.prec pf pg },
  case rfind : f pf hf { exact nat.partrec.rfind hf },
end

protected theorem some {f} : part.some partrec_in f := of_primrec f primrec.id

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
end

end rpartrec

end nat

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*} {τ : Type*} {μ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ] [primcodable τ] [primcodable μ]

def rpartrec (f : α →. σ) (g : β →. τ) := nat.rpartrec.reducible
(λ n, part.bind (decode α n) (λ a, (f a).map encode))
(λ n, part.bind (decode β n) (λ a, (g a).map encode))

infix ` partrec_in `:80 := rpartrec

def rpartrec_tot (f : α →. σ) (g : β → τ) := f partrec_in ↑ᵣg

infix ` partrec_in! `:80 := rpartrec_tot

def rpartrec₂ (f : α → β →. σ) (g : γ →. τ) := (λ x : α × β, f x.1 x.2) partrec_in g

infix ` partrec₂_in `:80 := rpartrec₂

def rpartrec₂_tot (f : α → β →. σ) (g : γ → τ) := f partrec₂_in ↑ᵣg

infix ` partrec₂_in! `:80 := rpartrec₂_tot

def rcomputable (f : α → σ) (g : β →. τ) := ↑ᵣf partrec_in g

infix ` computable_in `:80 := rcomputable

def rcomputable_tot (f : α → σ) (g : β → τ) := f computable_in ↑ᵣg

infix ` computable_in! `:80 := rcomputable_tot

def rcomputable₂ (f : α → β → σ) (g : γ →. τ) := (λ x : α × β, f x.1 x.2) computable_in g

infix ` computable₂_in `:80 := rcomputable₂

def rcomputable₂_tot (f : α → β → σ) (g : γ → τ) := f computable₂_in ↑ᵣg

infix ` computable₂_in! `:80 := rcomputable₂_tot

theorem partrec.to_rpart {f : α →. σ} {g : β →. τ} (h : partrec f) : f partrec_in g :=
nat.rpartrec.of_partrec _ h

theorem partrec.to_rpart_in {f : α →. σ} (g : β →. τ) (h : partrec f) : f partrec_in g :=
nat.rpartrec.of_partrec _ h

theorem computable.to_rcomp {f : α → σ} {g : β →. τ} (h : computable f) : f computable_in g :=
nat.rpartrec.of_partrec _ h

theorem computable.to_rcomp_in {f : α → σ} (g : β →. τ) (h : computable f) : f computable_in g :=
nat.rpartrec.of_partrec _ h

theorem primrec.to_rcomp {f : α → σ} {g : β →. τ} (h : primrec f) : f computable_in g :=
h.to_comp.to_rcomp

theorem primrec.to_rcomp_in {f : α → σ} (g : β →. τ) (h : primrec f) : f computable_in g :=
h.to_comp.to_rcomp

namespace rpartrec

theorem of_eq {f g : α →. σ} {h : β →. τ} (hf : f partrec_in h) (H : ∀ n, f n = g n) : g partrec_in h :=
(funext H : f = g) ▸ hf

theorem comp {f : β →. γ} {g : α → β} {h : σ →. τ} 
  (hf : f partrec_in h) (hg : g computable_in h) : (λ a, f (g a)) partrec_in h :=
(nat.rpartrec.comp hf hg).of_eq $ λ n, by simp; cases e : decode α n with a; simp [e, encodek]

theorem comp₂ {f : γ →. γ} {g : α → β → γ} {h : σ →. τ} 
  (hf : f partrec_in h) (hg : g computable₂_in h) : (λ a b, f (g a b)) partrec₂_in h :=
hf.comp hg

@[protected] lemma coe {o : σ →. τ} :
  (coe : option α →. α) partrec_in o := computable.id.of_option.to_rpart

@[protected] lemma some {o : σ →. τ} :
  (part.some : α →. α) partrec_in o := partrec.some.to_rpart

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

theorem nat_iff1 {f g} : f partrec_in g ↔ nat.rpartrec g f  :=
by simp[rpartrec, nat.rpartrec.reducible, encodable.encode, map]

theorem le_part_part {f : α →. σ} {g : β →. τ} : g partrec_in f → partrec f → partrec g :=
nat.rpartrec.le_part_part

theorem none {f : β →. τ} : (λ x, part.none : α →. σ) partrec_in f := partrec.none.to_rpart

theorem bind {f : α →. β} {g : α → β →. σ} {h : γ →. τ}
  (hf : f partrec_in h) (hg : g partrec₂_in h) : (λ a, (f a).bind (g a)) partrec_in h :=
(nat.rpartrec.comp hg (nat.rpartrec.some.pair hf)).of_eq $
λ n, by simp[(<*>)]; cases e : decode α n with a;
  simp [e, encodek]

theorem map {f : α →. β} {g : α → β → σ} {h : γ →. τ}
  (hf : f partrec_in h) (hg : g computable₂_in h) :
  (λ a, (f a).map (g a)) partrec_in h :=
by simpa [bind_some_eq_map] 
  using @rpartrec.bind _ _ _ _ _ _ _ _ _ _ _ (λ x y, part.some (g x y)) _ hf hg

theorem rfind {p : α → ℕ →. bool} {f : β →. σ} (hp : p partrec₂_in f) :
  (λ a, nat.rfind (p a)) partrec_in f :=
  have c₀ : (λ x, (p x.1 x.2).map (λ b, cond b 0 1) : α × ℕ →. ℕ) partrec_in f :=
    hp.map ((
      (primrec.dom_bool (λ b, cond b 0 1)).comp primrec.snd).to_comp.to_rpart),
((nat.rpartrec.rfind c₀).of_eq $ λ n, by 
{ cases e : decode α n with a;
  simp [e, nat.rfind_zero_none, map_id'],
  congr, funext n,
  simp [part.map_map, (∘)],
  apply map_id' (λ b, _),
  cases b; refl })

theorem rfind_refl {p : α → ℕ →. bool} : (λ a, nat.rfind (p a)) partrec_in prod.unpaired p :=
  have c₀ : (λ x : α × ℕ, (p x.1 x.2).map (λ b, cond b 0 1) : α × ℕ →. ℕ) partrec_in prod.unpaired p :=
    rpartrec.refl.map ((
      (primrec.dom_bool (λ b, cond b 0 1)).comp primrec.snd).to_comp.to_rpart),
((nat.rpartrec.rfind c₀).of_eq $ λ n, by 
{ cases e : decode α n with a;
  simp [e, nat.rfind_zero_none, map_id'],
  congr, funext n,
  simp [part.map_map, (∘)],
  apply map_id' (λ b, _),
  cases b; refl })

theorem of_option_refl {f : α → option β} : ↑ʳf partrec_in! f :=
((nat.rpartrec.of_partrec _ nat.partrec.ppred).comp nat.rpartrec.oracle).of_eq $ λ n, begin
  cases decode α n with a; simp,
  cases f a with b; simp,
end

theorem of_option {f : α → option σ} {g : β →. τ} 
  (h : f computable_in g) : ↑ʳf partrec_in g :=
of_option_refl.trans h

theorem of_option' {f : α → σ} {g : β →. τ} 
  (h : f computable_in g) : (λ x, part.some (f x)) partrec_in g :=
rpartrec.some.comp h

theorem to₂ {f : α × β →. σ} {g : γ →. τ} (hf : f partrec_in g) : (λ a b, f (a, b)) partrec₂_in g :=
hf.of_eq $ λ ⟨a, b⟩, rfl

end rpartrec

namespace rcomputable

theorem of_eq {f g : α → σ} {h : β →. τ} (hf : f computable_in h) (H : ∀ n, f n = g n) :
  g computable_in h := (funext H : f = g) ▸ hf

theorem le_comp_comp {f : α → σ} {g : β → τ} :
  g computable_in! f → computable f → computable g :=
nat.rpartrec.le_part_part

theorem comp {f : β → γ} {g : α → β} {h : σ →. τ} 
  (hf : f computable_in h) (hg : g computable_in h) : (λ a, f (g a)) computable_in h :=
(nat.rpartrec.comp hf hg).of_eq $ λ n, by simp; cases e : decode α n with a; simp [e, encodek]

theorem comp₂ {f : γ → σ} {g : α → β → γ} {o : τ →. μ} 
  (hf : f computable_in o) (hg : g computable₂_in o) :
  (λ a b, f (g a b)) computable₂_in o := hf.comp hg

theorem nat_elim
  {f : α → ℕ} {g : α → σ} {h : α × ℕ × σ → σ} {o : β →. γ}
  (hf : f computable_in o) (hg : g computable_in o) (hh : h computable_in o) :
  (λ a, (f a).elim (g a) (λ y IH, h (a, y, IH))) computable_in o :=
((rpartrec.nat_elim hf hg hh).of_eq) $
λ a, by { simp, induction f a with m, simp, simp[ih] }

theorem nat_elim'
  {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ → σ} {o : β →. γ}
  (hf : f computable_in o) (hg : g computable_in o) (hh : prod.unpaired3 h computable_in o) :
  (λ a, (f a).elim (g a) (h a)) computable_in o :=
((rpartrec.nat_elim hf hg hh).of_eq) $
λ a, by { simp, induction f a with m, simp, simp[ih] }

theorem id {f : β →. σ} : (@id α) computable_in f := computable.id.to_rcomp

theorem id' {f : β →. σ} : (λ x : α, x) computable_in f := computable.id.to_rcomp

theorem fst {f : γ →. σ} : (@prod.fst α β) computable_in f := computable.fst.to_rcomp

theorem snd {f : γ →. σ} : (@prod.snd α β) computable_in f := computable.snd.to_rcomp

theorem to_unary₁ {f : α → γ} {o : τ →. μ}
  (hf : f computable_in o) : (λ (x : α) (y : β), f x) computable₂_in o := hf.comp rcomputable.fst

theorem to_unary₂ {f : β → γ} {o : τ →. μ}
  (hf : f computable_in o) : (λ (x : α) (y : β), f y) computable₂_in o := hf.comp rcomputable.snd

theorem pair {f : α → σ} {g : α → τ} {h : γ →. μ}
  (hf : f computable_in h) (hg : g computable_in h) : (λ x, (f x, g x)) computable_in h :=
  (nat.rpartrec.pair hf hg).of_eq $ λ n, by cases decode α n; simp [(<*>)]

theorem const (a : α) {f : γ →. σ} : (λ x, a : β → α) computable_in f :=
(computable.const a).to_rcomp

protected theorem encode {f : β →. σ} : (@encode α _) computable_in f := computable.encode.to_rcomp

protected theorem decode {f : β →. σ} : (@decode α _) computable_in f := computable.decode.to_rcomp

@[refl] theorem refl {f : α → β} : f computable_in (f : α →. β) := nat.rpartrec.refl
theorem refl_in (f : α → β) : f computable_in (f : α →. β) := nat.rpartrec.refl

@[trans] theorem trans {f : α → σ} {g : β → τ} {h : γ →. μ} :
  f computable_in (g : β →. τ) → g computable_in h → f computable_in h := nat.rpartrec.trans

protected theorem cond {c : α → bool} {f : α → σ} {g : α → σ} {h : β →. τ}
  (hc : c computable_in h) (hf : f computable_in h) (hg : g computable_in h) :
  (λ a, cond (c a) (f a) (g a)) computable_in h :=
begin
  let f₀ := (λ a, cond a.1 a.2.1 a.2.2 : bool × σ × σ → σ),
  let f₁ := (λ a, (c a, f a, g a) : α → bool × σ × σ),
  have c₀ : computable f₀ := 
    computable.cond computable.fst 
      (computable.fst.comp computable.snd) (computable.snd.comp computable.snd),
  have c₁ : f₁ computable_in h := pair hc (pair hf hg),
  exact c₀.to_rcomp.comp c₁
end

theorem encode_iff {f : α → σ} {g : β →. τ}: (λ a, encodable.encode (f a)) computable_in g ↔ f computable_in g :=
iff.rfl

theorem option_some_iff {f : α → σ} {g : β →. τ} : (λ a, some (f a)) computable_in g ↔ f computable_in g :=
⟨λ h, encode_iff.1 $ primrec.pred.to_comp.to_rcomp.comp $ encode_iff.2 h,
 computable.option_some.to_rcomp.comp⟩

theorem to₂ {f : α × β → σ} {g : γ →. τ} (hf : f computable_in g) : (λ a b, f (a, b)) computable₂_in g :=
hf.of_eq $ λ ⟨a, b⟩, rfl

end rcomputable

namespace rpartrec₂

theorem of_eq {f g : α → β →. σ} {h : β →. τ} (hf : f partrec₂_in h) (H : ∀ n m, f n m = g n m) : g partrec₂_in h :=
(funext (λ n, funext (H n)) : f = g) ▸ hf

theorem unpaired {f : α → β →. σ} {o : τ →. μ} : (prod.unpaired f) partrec_in o ↔ f partrec₂_in o :=
by simp[rpartrec₂]

theorem comp  {f : β → γ →. σ} {g : α → β} {h : α → γ} {o : τ →. μ} 
  (hf : f partrec₂_in o) (hg : g computable_in o) (hh : h computable_in o) :
  (λ x, f (g x) (h x)) partrec_in o := rpartrec.comp hf (hg.pair hh)

theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ} {o : τ →. μ} 
  (hf : f partrec₂_in o) (hg : g computable₂_in o) (hh : h computable₂_in o) :
  (λ a b, f (g a b) (h a b)) partrec₂_in o := hf.comp hg hh

end rpartrec₂

namespace rpartrec
open rcomputable

theorem rfind_opt {f : α → ℕ → option σ} {g : β →. τ}
  (hf : f computable₂_in g) :
  (λ a, nat.rfind_opt (f a)) partrec_in g :=
(rfind (rpartrec.some.comp₂ (rcomputable.comp₂ (primrec.option_is_some.to_comp.to_rcomp) hf))).bind (of_option hf)

theorem nat_cases_right
  {f : α → ℕ} {g : α → σ} {h : α × ℕ →. σ} {o : γ →. τ}
  (hf : f computable_in o) (hg : g computable_in o) (hh : h partrec_in o) :
  (λ a, (f a).cases (some (g a)) (λ x, h (a, x))) partrec_in o :=
(nat_elim hf hg (hh.comp $ fst.pair (computable.pred.to_rpart.comp $ hf.comp fst))).of_eq $
λ a, begin
  simp, cases f a; simp,
  refine ext (λ b, ⟨λ H, _, λ H, _⟩),
  { rcases mem_bind_iff.1 H with ⟨c, h₁, h₂⟩, exact h₂ },
  { have : ∀ m, (nat.elim (part.some (g a))
      (λ y IH, IH.bind (λ _, h (a, n))) m).dom,
    { intro, induction m; simp [*, H.fst] },
    exact ⟨⟨this n, H.fst⟩, H.snd⟩ }
end

theorem to_unary₁ {f : α →. γ} {o : τ →. μ}
  (hf : f partrec_in o) : (λ (x : α) (y : β), f x) partrec₂_in o := hf.comp rcomputable.fst

theorem to_unary₂ {f : β →. γ} {o : τ →. μ}
  (hf : f partrec_in o) : (λ (x : α) (y : β), f y) partrec₂_in o := hf.comp rcomputable.snd

end rpartrec

namespace rcomputable
open rpartrec

theorem comp₂' {f : β × γ → σ} {g : α → β} {h : α → γ} {o : τ →. μ} 
  (hf : f computable_in o) (hg : g computable_in o) (hh : h computable_in o) :
  (λ a, f (g a, h a)) computable_in o :=
hf.comp (hg.pair hh)

theorem nat_cases {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ} {o : β →. τ}
  (hf : f computable_in o) (hg : g computable_in o) (hh : h computable₂_in o) :
  (λ a, (f a).cases (g a) (h a)) computable_in o :=
nat_elim hf hg (hh.comp $ fst.pair $ fst.comp snd)

theorem bind_decode_iff {f : α × β → option σ} {h : γ →. τ} : 
  (λ x : α × ℕ, (decode β x.2).bind (λ y, f (x.1, y))) computable_in h ↔ f computable_in h :=
⟨λ hf, nat.rpartrec.of_eq
    (((partrec.nat_iff.2 (nat.partrec.ppred.comp $
        nat.partrec.of_primrec $ primcodable.prim β)).comp computable.snd).to_rpart.bind (rpartrec.to_unary₁ hf)) $
  λ n, by simp;
    cases decode α n.unpair.1; simp;
    cases decode β n.unpair.2; simp,
λ hf, begin
  have H : (λ (a : (α × ℕ) × ℕ), part.map (λ (x : β), f (a.fst.fst, x)) ↑(encodable.decode β a.snd)) partrec_in h,
  { exact (rpartrec.coe.comp rcomputable.decode.to_unary₂).map
  (rcomputable.comp₂ hf ((rcomputable.to_unary₁ rcomputable.fst.to_unary₁).pair rcomputable.id'.to_unary₂)) },
  have : (λ a : α × ℕ, (encode (decode β a.2)).cases
    (some option.none) (λ n, part.map (λ x, f (a.1, x)) (decode β n))) partrec_in h :=
  nat_cases_right (primrec.encdec.to_comp.comp computable.snd).to_rpart
    (const option.none) H,
  refine this.of_eq (λ a, _),
  simp, cases decode β a.2; simp [encodek]
end⟩

theorem map_decode_iff {f : α × β → σ} {h : γ →. τ} : 
  (λ x : α × ℕ, (decode β x.2).map (λ y, f (x.1, y))) computable_in h ↔ f computable_in h :=
have this : (λ x : α × ℕ, (decode β x.2).bind (λ y, some $ f (x.1, y))) computable_in h ↔ f computable_in h :=
  (bind_decode_iff.trans option_some_iff), this

theorem option_cases {o : α → option β} {f : α → σ} {g : α → β → σ} {h : γ →. τ}
  (ho : o computable_in h) (hf : f computable_in h) (hg : g computable₂_in h) :
  @rcomputable _ _ σ _ _ _ _ _ (λ a, option.cases_on (o a) (f a) (g a)) h :=
option_some_iff.1 $
(nat_cases (encode_iff.2 ho) (option_some_iff.2 hf)
    (map_decode_iff.2 hg).to₂).of_eq $
λ a, by cases o a; simp [encodek]; refl

theorem option_bind {f : α → option β} {g : α → β → option σ} {h : γ →. τ}
  (hf : f computable_in h) (hg : g computable₂_in h) :
  (λ a, (f a).bind (g a)) computable_in h :=
(option_cases hf (const option.none) hg.to₂).of_eq $
λ a, by cases f a; refl

theorem option_map {f : α → option β} {g : α → β → σ} {h : γ →. τ}
  (hf : f computable_in h) (hg : g computable₂_in h) :
  (λ a, (f a).map (g a)) computable_in h :=
option_bind hf (primrec.option_some.to_comp.to_rcomp.comp hg).to₂

theorem total_computable {f : α →. σ} (h : ∀ a, (f a).dom) :
  (λ a, (f a).get (h a)) computable_in f := (rpartrec.refl.of_eq $ by simp)

end rcomputable

namespace rcomputable₂
open rcomputable

theorem comp {f : γ → δ → σ} {g : α → γ} {h : α → δ} {o : τ →. μ} 
  (hf : f computable₂_in o) (hg : g computable_in o) (hh : h computable_in o) :
  (λ a, f (g a) (h a)) computable_in o := hf.comp (hg.pair hh)

theorem comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} {o : τ →. μ} 
  (hf : f computable₂_in o) (hg : g computable₂_in o) (hh : h computable₂_in o) :
  (λ a b, f (g a b) (h a b)) computable₂_in o := rcomputable.comp hf (hg.pair hh)

theorem pair {f : α → β → γ} {g : α → β → δ} {o : τ →. μ}
  (hf : f computable₂_in o) (hg : g computable₂_in o) :
  (λ x y, (f x y, g x y)) computable₂_in o := rcomputable.pair hf hg

end rcomputable₂

lemma rfind_dom_total {p : ℕ → bool} :
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
      intros l el, simp [part.some] },
    { use 0, exact ⟨eq.symm ep, by simp⟩ } }
end

lemma nat_bool_minimum {n : ℕ} : ∀ {p : ℕ → bool}, p n = tt → (∃ m, p m = tt ∧ ∀ l, l < m → p l = ff) :=
begin
  induction n with n0 ih,
  { assume p h, use 0, exact ⟨h, by simp⟩ },
  { assume p h, 
    let q := (λ n : ℕ, (p n.succ)),
    have q0 : q n0 = tt, simp[q], exact h,
    rcases ih q0 with ⟨m, qm, hm⟩, simp[q] at qm, simp[q] at hm,
    cases ep : p 0 with p0 p0,
    { use m.succ, split, exact qm,
      intros l el, cases l, exact ep,
      exact hm _ (show l < m, by omega) },
    { use 0, exact ⟨ep, by simp⟩ } }
end

lemma nat_bool_minimum' {n : ℕ} : ∀ {p : ℕ → bool}, p n = tt → (∃ m, m ≤ n ∧ p m = tt ∧ ∀ l, l < m → p l = ff) :=
begin
  intros p h, rcases nat_bool_minimum h with ⟨m, mh⟩, use m,
  have l : m ≤ n,
  { cases (nat.lt_or_ge n m) with em em, exfalso,
    have c : p n = ff := mh.2 _ em, exact bool_iff_false.mpr c h,
    exact em },
  exact ⟨l, mh⟩
end