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

lemma relation_path_lt {α} {p : ℕ → α} (R : α → α → Prop)
  (t : ∀ a b c, R a b → R b c → R a c)
  (i : ∀ n, R (p (n+1)) (p n)) : 
  ∀ s t, s < t → R (p t) (p s) :=
begin
  have l0 : ∀ s t, R (p (s + t + 1)) (p s),
  { intros s t, induction t with s0 IH generalizing s, simp[i],
    simp[show s + s0.succ = (s + s0) + 1, from nat.add_succ _ _],
    exact t _ _ _ (i _) (IH _) },
  intros s t e,
  have : t = s + (t - s - 1) + 1, omega,
  rw this, exact l0 _ _,
end



section
namespace strategy
namespace order

class has_prec (α : Type*) :=
(prec  : α → α → Prop)
(trans : transitive prec)
(wf    : well_founded prec)

infix ` ≺ `:80 := has_prec.prec
variables {Λ : Type*}
variables [has_prec Λ]

theorem has_prec.prec.trans : ∀ {a b c : Λ}, a ≺ b → b ≺ c → a ≺ c := has_prec.trans

lemma has_prec.induction {C : Λ → Prop} (a : Λ) (h : ∀ x, (∀ y, y ≺ x → C y) → C x) : C a :=
has_prec.wf.induction a h

lemma has_prec.minimal {C : Λ → Prop} (h : ∃ x, C x) : ∃ m, C m ∧ ∀ x, x ≺ m → ¬C x:=
begin
  suffices : ∀ a, C a → ∃ (m : Λ), C m ∧ ∀ (x : Λ), x ≺ m → ¬C x,
  { rcases h with ⟨a, ha⟩, refine this _ ha },
  intros a,
  apply has_prec.induction a,
  intros a IH Ca,
  by_cases C : ∃ b, b ≺ a ∧ C b,
  { rcases C with ⟨b, hyp_b, hyp_b1⟩, refine IH b hyp_b hyp_b1 },
  { simp at C, refine ⟨a, Ca, C⟩ }
end

lemma has_prec.enum_minimal {α} [inhabited α] (f : α → Λ) : ∃ m, ∀ n, ¬f n ≺ f m :=
begin
  let C := (λ x : Λ, ∃ n, f n = x),
  have := @has_prec.minimal _ _ C ⟨f (default α), ⟨(default α), rfl⟩⟩,
  simp[C] at this, rcases this with ⟨w, hyp_w⟩,
  refine ⟨w, λ n A, _⟩, have := hyp_w (f n) A,
  have := this n, simp at this, exact this
end

lemma has_prec.antirefl {a : Λ} : ¬a ≺ a :=
by { have := has_prec.enum_minimal (λ n : ℕ, a), simp at this, exact this }

inductive option.prec {α : Type*} [has_prec α] : option α → option α → Prop
| none {a} : option.prec (some a) none
| some {a b} : a ≺ b → option.prec (some a) (some b)

lemma option.prec.trans {α : Type*} [has_prec α] : transitive (@option.prec α _) :=
λ a b c ab bc,
begin
  cases ab with a a b ab',
  { cases bc },
  { cases bc with _ _ c bc', exact option.prec.none,
    exact option.prec.some (ab'.trans bc'), }
end

lemma option.prec.wf {α : Type*} [has_prec α] : well_founded (@option.prec α _) :=
well_founded.intro (λ a, acc.intro a $ λ b ba,
  by { have : ∀ a : α, acc prec (some a),
       { intros a, apply has_prec.induction a,
         intros x IH, refine acc.intro _ (λ y yx, _),
         cases yx with _ z _ zx, apply IH _ zx },
       cases ba with b b a ba; exact this _ })

inductive bool.prec : bool → bool → Prop
| intro : bool.prec tt ff

lemma bool.prec.trans : transitive bool.prec := λ _ _ _ ab bc, by cases ab; cases bc

lemma bool.prec.wf : well_founded bool.prec :=
well_founded.intro (λ a, acc.intro a $ λ b ba,
  by { cases ba, refine acc.intro _ (λ c ctt, _), cases ctt })

instance {α : Type*} [has_prec α] : has_prec (option α) := ⟨option.prec, option.prec.trans, option.prec.wf⟩

instance : has_prec bool := ⟨bool.prec, bool.prec.trans, bool.prec.wf⟩

instance : has_prec ℕ := ⟨(<), @nat.lt_trans, nat.lt_wf⟩

def kb_order (p q : ℕ → Λ) : Prop := ∃ u : ℕ,  
(∀ ⦃n⦄, n < u → p n = q n) ∧ p u ≺ q u

infix ` <KB `:80 := kb_order

theorem kb_order.trans {p₀ p₁ p₂ : ℕ → Λ} :
  p₀ <KB p₁ → p₁ <KB p₂ → p₀ <KB p₂ :=
begin
  rintros ⟨u₀, hyp_u₀, hyp_u₀1⟩,
  rintros ⟨u₁, hyp_u₁, hyp_u₁1⟩,
  refine ⟨min u₀ u₁, λ n eqn_n, _, _⟩,
  simp at eqn_n, simp [hyp_u₀ eqn_n.1, hyp_u₁ eqn_n.2],
  have : u₀ < u₁ ∨ u₀ = u₁ ∨ u₁ < u₀, from trichotomous _ _, cases this,
  { simp [le_of_lt this, ←(hyp_u₁ this), hyp_u₀1] }, cases this,
  { simp [this] at hyp_u₀1 ⊢, exact hyp_u₀1.trans hyp_u₁1 },
  { simp [le_of_lt this, (hyp_u₀ this), hyp_u₁1] }
end

theorem kb_order_lim {p : ℕ → ℕ → Λ} [e : inhabited Λ]
  (h : ∀ s, p (s + 1) <KB p s) :
  ∃ f : ℕ → Λ, ∀ n, ∃ s, ∀ t, s < t → p t n = f n :=
begin
  have h' := relation_path_lt (<KB) (@kb_order.trans _ _) h,
  suffices :
    ∀ n₀, ∃ s, ∀ n, n ≤ n₀ → ∃ v, ∀ t, s < t → p t n = v,
  { have : ∀ n, ∃ v s, ∀ t, s < t → p t n = v,
    { intros n, rcases this n with ⟨s, hyp_s⟩, rcases hyp_s n (by refl) with ⟨v, hyp_v⟩,
      refine ⟨v, s, hyp_v⟩ },
    let f := (λ n, classical.epsilon $ λ v : Λ, ∃ s, ∀ t, s < t → p t n = v),
    have := λ n, classical.epsilon_spec (this n), simp at this, exact ⟨f, this⟩ },
  intros n₀, induction n₀ with n₀ IH, simp,
  { have : ∃ m, ∀ n, ¬p n 0 ≺ p m 0, from has_prec.enum_minimal (λ s, p s 0), 
    rcases this with ⟨m, lmm_m⟩,
    refine ⟨m, p m 0, λ t eqn_t, _⟩, 
    have : p t <KB p m, from h' _ _ eqn_t, rcases this with ⟨u, hyp_u, hyp_u1⟩,
    cases u, { have := lmm_m t, contradiction },
    exact @hyp_u 0 (by simp) },
  { rcases IH with ⟨s₀, IH⟩,
    have : ∃ m, ∀ t, ¬p (max (s₀ + 1) t) (n₀ + 1) ≺ p (max (s₀ + 1) m) (n₀ + 1),
    from has_prec.enum_minimal (λ s, p (max (s₀ + 1) s) (n₀ + 1)),
    rcases this with ⟨m, lmm_m⟩,
    let s₁ := max (s₀ + 1) m,    
    refine ⟨s₁, λ n eqn_n, _⟩,
    have : n ≤ n₀ ∨ n = n₀ + 1, from nat.of_le_succ eqn_n,
    cases this,
    { rcases IH _ this with ⟨v, lmm_v⟩, refine ⟨v, λ t eqn_t, _⟩, simp at eqn_t,
      have : s₀ < t, omega, exact lmm_v _ this },
    { refine ⟨p s₁ (n₀ + 1), λ t eqn_t, _⟩, simp[this],
      have : p t <KB p s₁, from h' _ _ eqn_t,
      rcases this with ⟨u, hyp_u, hyp_u1⟩,
      have : n₀ + 1 < u,
      { have C : u < n₀ + 1 ∨ u = n₀ + 1 ∨ n₀ + 1 < u, from trichotomous _ _,
        cases C,
        { exfalso,
          have C' : u ≤ n₀, from nat.lt_succ_iff.mp C,
          rcases IH _ C' with ⟨v, lmm_v⟩,
          have eqn_v1 := lmm_v _ (show s₀ < s₁, by simp[s₁]),
          have eqn_v2 := lmm_v t (lt_trans (show s₀ < s₁, by simp[s₁]) eqn_t),
          simp [eqn_v1, eqn_v2] at hyp_u1, exact has_prec.antirefl hyp_u1 }, cases C,
        { exfalso,
          simp[C] at hyp_u1, simp at eqn_t,
          have := lmm_m t, simp[le_of_lt eqn_t.1] at this,
          exact this hyp_u1 },
        exact C },
      exact hyp_u this } }
end

theorem kb_order_lim {p : ℕ → ℕ → Λ} [e : inhabited Λ]
  (h : ∀ s, p (s + 1) <KB p s) :
  ∃ f : ℕ → Λ, ∀ n, ∃ s, ∀ t, s < t → p t n = f n :=
begin
  have h' := relation_path_lt (<KB) (@kb_order.trans _ _) h,
  suffices :
    ∀ n₀ n, n < n₀ → ∃ v s, ∀ t, s < t → p t n = v,
  { have : ∀ n, ∃ v s, ∀ t, s < t → p t n = v, from λ n, this (n+1) n (by simp),
    let f := (λ n, classical.epsilon $ λ v : Λ, ∃ s, ∀ t, s < t → p t n = v),
    have := λ n, classical.epsilon_spec (this n), simp at this, exact ⟨f, this⟩ },
  intros n, induction n with n IH,
  { have : ∃ m, ∀ n, ¬p n 0 ≺ p m 0, from has_prec.enum_minimal (λ s, p s 0), 
    rcases this with ⟨m, lmm_m⟩,
    refine ⟨p m 0, m, λ t eqn_t, _⟩, 
    have : p t <KB p m, from h' _ _ eqn_t, rcases this with ⟨u, hyp_u, hyp_u1⟩,
    cases u, { have := lmm_m t, contradiction },
    exact @hyp_u 0 (by simp) },
  { rcases IH with ⟨v₀, s₀, IH⟩,
    have : ∃ m, ∀ t, ¬p (max s₀ t) (n + 1) ≺ p (max s₀ m) (n + 1),
    from has_prec.enum_minimal (λ s, p (max s₀ s) (n+1)),
    rcases this with ⟨m, lmm_m⟩,
    refine ⟨p (max s₀ m) (n + 1), max s₀ m, λ t eqn_t, _⟩,
    have : p t <KB p (max s₀ m), from h' _ _ eqn_t,
    rcases this with ⟨u, hyp_u, hyp_u1⟩,
    have : n + 1 < u,
    { have eqn_u : u < n + 1 ∨ u = n + 1 ∨ n + 1 < u, from trichotomous _ _,
      cases eqn_u,
      { exfalso,  } }


      }
end

theorem kb_order_lim {p : ℕ → ℕ → Λ}
  (h : ∀ n, p n <KB p (n+1)) :
  ∀ s, ∃ n, ∀ m, n < m → p n s = p m s := λ s,
begin
  have h' := relation_path_lt (<KB) (@kb_order.trans _ _) h,
  induction s,
  
end


def list.kb (l₀ l₁ : list Λ) := ∃ u : ℕ, 
(∀ ⦃n⦄, n < u → l₀.nth n = l₁.nth n) ∧
(l₀.nth u ≺ l₁.nth u)

infix ` <KB `:80 := list.kb


def list.kbeq (l₀ l₁ : list Λ) := l₀ = l₁ ∨ l₀ <KB l₁

infix ` ≤KB `:80 := list.kbeq

theorem kb_le {l₀ l₁ : list Λ} (h : l₁ <KB l₀) {n a b} :
  l₁.nth n = some b → l₀.nth n = some a → b ≺ a :=


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
(r = none) && cond m.bodd (⟦m.div2⟧^A₁.fdecode [s] x = some ff) (⟦m.div2⟧^A₀.fdecode [s] x = some ff)

def renovate (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  list (ℕ × bool) × list (ℕ × bool) :=
let A₀ := A.1,
    A₁ := A.2,
    x  := (δ.inth m).2.1,
    r  := (δ.inth m).2.2 in
cond m.bodd (A₀, (x, tt) :: A₁) ((x, tt) :: A₀, A₁) 

def init (s : ℕ) (δ : list (bool × ℕ × option ℕ)) : bool × ℕ × option ℕ :=
(ff, (s), none)

def inititr (s : ℕ) (δ : list (bool × ℕ × option ℕ)) : ℕ → list (bool × ℕ × option ℕ)
| 0     := δ
| (n+1) := inititr n ++ [init s (inititr n)]

def initialize (s : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  bool × ℕ × option ℕ := init s δ

def revise (s m : ℕ) (A : list (ℕ × bool) × list (ℕ × bool)) (δ : list (bool × ℕ × option ℕ)) :
  list (bool × ℕ × option ℕ) :=
let x  := (δ.inth m).2.1,
    r  := (δ.inth m).2.2 in
inititr s ((δ.take m) ++ [(tt, x, s)]) (s-m)

def prec (x y : (bool × ℕ × option ℕ)) : Prop := x.1 ≺ y.1

local attribute [instance]
theorem Λ_prec : has_prec (bool × ℕ × option ℕ) := ⟨prec⟩

def approx := strategy.approx ([], []) attention renovate initialize revise
#check approx
#eval approx 15
#eval ⟦5⟧ᵪ^(approx 15).1.2.fdecode [11] 10
#eval (approx 15).1.1.fdecode 10
end FM