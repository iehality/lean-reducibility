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

end

#check @list.prec