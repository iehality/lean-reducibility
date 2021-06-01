import reducibility function

open encodable denumerable roption t_reducible

local attribute [simp] set.set_of_app_iff

lemma list.append_nth_some {α} {l₀ : list α} {n a} (h : l₀.nth n = some a) (l₁) :
  (l₀ ++ l₁).nth n = some a :=
by { have := list.nth_eq_some.mp h, rcases this with ⟨en, _⟩,
     exact eq.trans (list.nth_append en) h, }

lemma list.drop_nth {α} : ∀ (l : list α) (k n), (l.drop k).nth n = l.nth (n + k)
| []        _       _ := by simp [list.drop]
| (l :: ls) 0       _ := by simp [list.drop]
| (l :: ls) (k + 1) n := 
    by { simp [list.drop], have := list.drop_nth ls k n, simp [this], exact rfl }

lemma relation_path_le {α} {p : ℕ → α} (R : α → α → Prop)
  (r : ∀ a, R a a) (t : ∀ a b c, R a b → R b c → R a c)
  (i : ∀ n, R (p n) (p (n+1))) : 
  ∀ s t, s ≤ t → R (p s) (p t) :=
begin
  have l0 : ∀ s t, R (p s) (p (s + t)),
  { intros s t, induction t with s0 ih generalizing s, simp[r],
    simp[show s + s0.succ = (s + s0) + 1, from nat.add_succ _ _],
    exact t _ _ _ (ih _) (i _) },
  intros s t e,
  have : t = s + (t - s), omega,
  rw this, exact l0 _ _,
end

class has_prec (α : Type*) := (prec : α → α → Prop)

infix ` ≺ `:80 := has_prec.prec

inductive option.prec {α : Type*} [has_prec α] : option α → option α → Prop
| none {a} : option.prec none (some a)
| some {a b} : a ≺ b → option.prec (some a) (some b)

inductive bool.prec : bool → bool → Prop
| intro : bool.prec ff tt

instance {α : Type*} [has_prec α] : has_prec (option α) := ⟨option.prec⟩

instance : has_prec bool := ⟨bool.prec⟩

section
namespace strategy
namespace order

variables {Λ : Type*}
variables [has_prec Λ]

def list.prec (l₀ l₁ : list Λ) := ∃ a b l,
  a :: l <:+ l₀ ∧ b :: l <:+ l₁ ∧ a ≺ b
  
infix ` <L `:50 := list.prec

def list.kb (l₀ l₁ : list Λ) := ∃ u : ℕ, 
(∀ n, n < u → l₀.rnth n = l₁.rnth n) ∧
(l₀.rnth u ≺ l₁.rnth u)

infix ` <KB `:80 := list.kb

def list.kbeq (l₀ l₁ : list Λ) := l₀ = l₁ ∨ l₀ <KB l₁

infix ` ≤KB `:80 := list.kbeq

end order

section 
parameters {Λ : Type*} [has_prec Λ] {α : Type*}
  (head       : α)
  (attention  : ℕ → ℕ → α → list Λ → bool)
  (renovate   : ℕ → ℕ → α → list Λ → α)
  (initialize : ℕ → α → list Λ → Λ)
  (revise     : ℕ → ℕ → α → list Λ → list Λ)

def approx : ℕ → α × list Λ
| 0     := (head, [])
| (s+1) := let a := (approx s).1,
               δ := (approx s).2,
               m := nat.rfind_fin (λ m, attention s m a δ) s in
  match m with
  | none   := (a, δ ++ [initialize s a δ])
  | some m := (renovate s m a δ, revise s m a δ)
  end

def revise_wellorder : Prop := ∀ s m a δ, revise s m a δ ≤KB δ


end
end strategy
end
section FM

/- Λ := bool × ℕ × option ℕ -/

def attention (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) : bool :=
let A₀ := A.1,
    A₁ := A.2,
    x  := (δ.inth m).2.1,
    r  := (δ.inth m).2.2 in
(r = none) && cond m.bodd (⟦m.div2⟧^A₀.fdecode [s] x = some ff) (⟦m.div2⟧^A₁.fdecode [s] x = some ff)

def renovate (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  list (ℕ × bool) × list (ℕ × bool) :=
let A₀ := A.1,
    A₁ := A.2,
    x  := (δ.inth m).2.1,
    r  := (δ.inth m).2.2 in
cond m.bodd ((x, tt) :: A₀, A₁) (A₀, (x, tt) :: A₁)

def init (s : ℕ) (δ : list (bool × ℕ × option ℕ)) : bool × ℕ × option ℕ :=
(ff, ((encode δ).mkpair s), none)

def inititr (s : ℕ) (δ : list (bool × ℕ × option ℕ)) : ℕ → list (bool × ℕ × option ℕ)
| 0     := δ
| (n+1) := inititr n ++ [init s (inititr n)]

def initialize (s : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  bool × ℕ × option ℕ := init s δ

def revise (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  list (bool × ℕ × option ℕ) :=
let x  := (δ.inth m).2.1,
    r  := (δ.inth m).2.2 in
inititr s ((δ.take m) ++ [(tt, x, s)]) s

def prec (x y : (bool × ℕ × option ℕ)) : Prop := x.1 ≺ y.1

instance : has_prec (bool × ℕ × option ℕ) := ⟨prec⟩

def approx := strategy.approx ([], []) attention renovate initialize revise
#check strategy.approx
end FM