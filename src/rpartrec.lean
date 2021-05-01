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
    nat.rpartrec.code.evaln a.unpair.1 f.eval_opt (of_nat _ a.unpair.2) n)

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
  case univn : _ _ _ pf { exactI univn pf },
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

end rpartrec