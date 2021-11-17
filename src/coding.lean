import computability.partrec
import computability.partrec_code
import data.pfun
import tactic
import rpartrec
import rcomputability_tactic

open encodable denumerable part

@[simp] lemma eval_eval_opt {α β} (f : α →. β) [D : decidable_pred f.dom] {x} :
  @pfun.eval_opt _ _ f D x = @part.to_option _ (f x) (D x) := rfl

@[simp] theorem mem_to_option' {α} {o : part α} [decidable o.dom] {a : α} :
  to_option o = some a ↔ a ∈ o := mem_to_option

theorem mem_to_option_none {α} {o : part α} [D : decidable o.dom] {a : α} :
  to_option o = none ↔ o = none :=
by { unfold to_option, by_cases h : o.dom; simp [h],
     { exact λ h0, part.eq_none_iff'.mp h0 h },
     { exact part.eq_none_iff'.mpr h } }

namespace nat.rpartrec

inductive code : Type
| oracle : code
| zero   : code
| succ   : code
| left   : code
| right  : code
| pair   : code → code → code
| comp   : code → code → code
| prec   : code → code → code
| rfind' : code → code

end nat.rpartrec

namespace nat.rpartrec.code
open nat (mkpair unpair)
open nat.rpartrec (code)

protected def const : ℕ → code
| 0     := zero
| (n+1) := comp succ (const n)

protected def id : code := pair left right

def curry (c : code) (n : ℕ) : code :=
comp c (pair (code.const n) code.id)

def ctrans (c : code) : code → code
| oracle       := c
| zero         := zero
| succ         := succ
| left         := left
| right        := right
| (pair cf cg) := pair (ctrans cf) (ctrans cg)
| (comp cf cg) := comp (ctrans cf) (ctrans cg)
| (prec cf cg) := prec (ctrans cf) (ctrans cg)
| (rfind' cf)  := rfind' (ctrans cf)

def encode_code : code → ℕ
| oracle       := 0
| zero         := 1
| succ         := 2
| left         := 3
| right        := 4
| (pair cf cg) := (bit0 $ bit0 (mkpair (encode_code cf) (encode_code cg))) + 5
| (comp cf cg) := (bit0 $ bit1 (mkpair (encode_code cf) (encode_code cg))) + 5
| (prec cf cg) := (bit1 $ bit0 (mkpair (encode_code cf) (encode_code cg))) + 5
| (rfind' cf)  := (bit1 $ bit1 (encode_code cf)) + 5

def of_nat_code : ℕ → code
| 0 := oracle
| 1 := zero
| 2 := succ
| 3 := left
| 4 := right
| (e+5) :=
  have div8 : e.div2.div2 ≤ e :=
    by { simp[nat.div2_val], exact le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2) },
  have e.div2.div2 < e + 5 := nat.lt_succ_iff.mpr (le_trans div8 (nat.le.intro rfl)),
  have e.div2.div2.unpair.1 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_left_le _) div8) (nat.le.intro rfl)),
  have e.div2.div2.unpair.2 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_right_le _) div8) (nat.le.intro rfl)),
  match e.bodd, e.div2.bodd with
  | ff, ff := pair (of_nat_code e.div2.div2.unpair.1)
    (of_nat_code e.div2.div2.unpair.2)
  | ff, tt := comp (of_nat_code e.div2.div2.unpair.1)
    (of_nat_code e.div2.div2.unpair.2)
  | tt, ff := prec (of_nat_code e.div2.div2.unpair.1)
    (of_nat_code e.div2.div2.unpair.2)
  | tt, tt := rfind' (of_nat_code e.div2.div2)
  end

private lemma encode_of_nat_code : ∀ e, encode_code (of_nat_code e) = e
| 0     := by simp[of_nat_code, encode_code]
| 1     := by simp[of_nat_code, encode_code]
| 2     := by simp[of_nat_code, encode_code]
| 3     := by simp[of_nat_code, encode_code]
| 4     := by simp[of_nat_code, encode_code]
| (e+5) :=
have div8 : e.div2.div2 ≤ e :=
    by { simp[nat.div2_val], 
         exact le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2) },
  have e.div2.div2 < e + 5 := nat.lt_succ_iff.mpr (le_trans div8 (nat.le.intro rfl)),
  have e.div2.div2.unpair.1 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_left_le _) div8) (nat.le.intro rfl)),
  have e.div2.div2.unpair.2 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_right_le _) div8) (nat.le.intro rfl)),
  have IH : _ := encode_of_nat_code e.div2.div2,
  have IH1 : _ := encode_of_nat_code e.div2.div2.unpair.1,
  have IH2 : _ := encode_of_nat_code e.div2.div2.unpair.2,
  begin
    suffices :
      (of_nat_code (e + 5)).encode_code =
      nat.bit e.bodd (nat.bit e.div2.bodd e.div2.div2) + 5,
    { simp[nat.bit_decomp, this] },
    simp [encode_code, of_nat_code],
    cases e.bodd; cases e.div2.bodd;
    simp [encode_code, of_nat_code, nat.bit, IH, IH1, IH2],
  end

private lemma of_nat_code_encode : ∀ c, of_nat_code (encode_code c) = c
| oracle       := by simp[of_nat_code, encode_code]
| zero         := by simp[of_nat_code, encode_code]
| succ         := by simp[of_nat_code, encode_code]
| left         := by simp[of_nat_code, encode_code]
| right        := by simp[of_nat_code, encode_code]
| (pair cf cg) := by { simp[encode_code, of_nat_code],
    exact ⟨of_nat_code_encode cf, of_nat_code_encode cg⟩ }
| (comp cf cg) := by { simp[encode_code, of_nat_code],
    exact ⟨of_nat_code_encode cf, of_nat_code_encode cg⟩ }
| (prec cf cg) := by { simp[encode_code, of_nat_code],
    exact ⟨of_nat_code_encode cf, of_nat_code_encode cg⟩ }
| (rfind' cf)  := by { simp[encode_code, of_nat_code],
    exact of_nat_code_encode cf }

instance : denumerable code := mk' ⟨encode_code, of_nat_code, of_nat_code_encode, encode_of_nat_code⟩

def evaln : ∀ (e : ℕ) (f : ℕ →. ℕ) [∀ x, decidable (f x).dom], code → ℕ → option ℕ
| 0     f _ _            := λ _, none
| (s+1) f _ oracle       := λ n, guard (n ≤ s) >> by exactI (f n).to_option
| (s+1) f _ zero         := λ n, guard (n ≤ s) >> pure 0
| (s+1) f _ succ         := λ n, guard (n ≤ s) >> pure (nat.succ n)
| (s+1) f _ left         := λ n, guard (n ≤ s) >> pure n.unpair.1
| (s+1) f _ right        := λ n, guard (n ≤ s) >> pure n.unpair.2
| (s+1) f D (pair cf cg) := λ n, guard (n ≤ s) >>
    by exactI mkpair <$> evaln (s+1) f cf n <*> evaln (s+1) f cg n
| (s+1) f D (comp cf cg) := λ n, guard (n ≤ s) >>
    do x ← by exactI evaln (s+1) f cg n, by exactI evaln (s+1) f cf x
| (s+1) f D (prec cf cg) := λ n, guard (n ≤ s) >>
    n.unpaired (λ a n,
    n.cases (by exactI evaln (s+1) f cf a) $ λ y, do
    i ← by exactI evaln s f (prec cf cg) (mkpair a y),
    by exactI evaln (s+1) f cg (mkpair a (mkpair y i)))
| (s+1) f D (rfind' cf)  := λ n, guard (n ≤ s) >>
    n.unpaired (λ a m, do
    x ← by exactI evaln (s+1) f cf (mkpair a m),
    if x = 0 then pure m else
    by exactI evaln s f (rfind' cf) (mkpair a (m+1)))
-- evaln s f c x = { c }ᶠₛ (x)

@[simp] theorem evaln_0 {f : ℕ →. ℕ} [∀ x, decidable (f x).dom] {c n} : evaln 0 f c n = none :=
by induction c; simp [evaln]

theorem evaln_inclusion : ∀ {s c} {f g : ℕ →. ℕ} [∀ x, decidable (f x).dom] [∀ x, decidable (g x).dom],
by exactI  (∀ x y, x < s → y ∈ f x → y ∈ g x) → 
  ∀ {x y}, evaln s f c x = some y → evaln s g c x = some y
| 0     c            _ _ _  _  := by simp[evaln]
| (s+1) oracle       f g _  _  := λ h n y, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega,
         cases this; simp[(>>), this], exact h _ _ (nat.lt_succ_iff.mpr this),
         intros _ c, exfalso, exact option.not_mem_none _ c }
| (s+1) zero         f g _  _  := by simp[evaln]
| (s+1) succ         f g _  _  := by simp[evaln]
| (s+1) left         f g _  _  := by simp[evaln]
| (s+1) right        f g _  _  := by simp[evaln]
| (s+1) (pair cf cg) f g Df Dg := λ h n y,
    have IH₀ : _ := @evaln_inclusion (s+1) cf f g Df Dg h,
    have IH₁ : _ := @evaln_inclusion (s+1) cg f g Df Dg h,
    by { simp[evaln, (>>)], assume e hf,
         have : ∃ y, by exactI evaln (s + 1) f cf n = some y, 
         { cases (by exactI evaln (s + 1) f cf n); simp, { simp[(<*>), hf] at hf ⊢, exact hf } },
         rcases this with ⟨y0, hy0⟩, have IH₀' := IH₀ hy0,
          have : ∃ y, by exactI evaln (s + 1) f cg n = some y, 
         { cases (by exactI evaln (s + 1) f cg n); simp, { simp[(<*>), hf] at hf ⊢, exact hf } },
         rcases this with ⟨y1, hy1⟩, have IH₁' := IH₁ hy1,
         simp[hy0, hy1, IH₀', IH₁'] at hf ⊢, exact ⟨e, hf⟩ }
| (s+1) (comp cf cg) f g Df Dg := λ h n y,
    have IH₀ : _ := @evaln_inclusion (s+1) cf f g Df Dg h,
    have IH₁ : _ := @evaln_inclusion (s+1) cg f g Df Dg h,
    by { simp[evaln, (>>)], assume e z hz hy,
         refine ⟨e, z, IH₁ hz, IH₀ hy⟩ }
| (s+1) (prec cf cg) f g Df Dg := λ h n y,
    have l0 : ∀ x y, x < s → y ∈ f x → y ∈ g x :=
      λ x y e, h x y (nat.lt.step e),
    have IH₀ : _ := @evaln_inclusion s (cf.prec cg) f g Df Dg l0,
    have IH₁ : _ := @evaln_inclusion (s+1) cf f g Df Dg h,
    have IH₂ : _ := @evaln_inclusion (s+1) cg f g Df Dg h,
    by { simp[evaln, (>>)], assume e hf,
         cases n.unpair.snd with n0; simp at hf ⊢, exact ⟨e, IH₁ hf⟩,
         rcases hf with ⟨z, hz0, hz1⟩,
         refine ⟨e, z, IH₀ hz0, IH₂ hz1⟩ }
| (s+1) (rfind' cf)  f g Df Dg := λ h n y, 
    have l0 : ∀ x y, x < s → y ∈ f x → y ∈ g x :=
      λ x y e, h x y (nat.lt.step e),
    have IH₀ : _ := @evaln_inclusion (s+1) cf f g Df Dg h, 
    have IH₁ : _ := @evaln_inclusion s cf.rfind' f g Df Dg l0,
    by { simp[evaln, (>>)], assume e z ez ey,
         refine ⟨e, z, IH₀ ez, _⟩,
         cases z with z0; simp at ey ⊢, exact ey, exact IH₁ ey }

theorem evaln_use : ∀ {s c} {f g : ℕ →. ℕ} [∀ x, decidable (f x).dom] [∀ x, decidable (g x).dom],
  by exactI (∀ x, x < s → f x = g x) → evaln s f c = evaln s g c
| 0     c            _ _ _  _  := by simp[evaln]
| (s+1) oracle       f g _  _  := λ h, funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬n ≤ s, omega,
         cases this; simp[(>>), this], exact h n (nat.lt_succ_iff.mpr this), refl }
| (s+1) zero         f g _  _ := by simp[evaln]
| (s+1) succ         f g _  _ := by simp[evaln]
| (s+1) left         f g _  _ := by simp[evaln]
| (s+1) right        f g _  _ := by simp[evaln]
| (s+1) (pair cf cg) f g Df Dg := λ h,
    have IH₀ : _ := @evaln_use (s+1) cf f g Df Dg h,
    have IH₁ : _ := @evaln_use (s+1) cg f g Df Dg h,
    funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀, IH₁] }
| (s+1) (comp cf cg) f g Df Dg := λ h,
    have IH₀ : _ := @evaln_use (s+1) cf f g Df Dg h,
    have IH₁ : _ := @evaln_use (s+1) cg f g Df Dg h,
    funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀, IH₁] }
| (s+1) (prec cf cg) f g Df Dg := λ h,
    have l0 : ∀ (x : ℕ), x < s → f x = g x := λ x e, h x (nat.lt.step e),
    have IH₀ : _ := @evaln_use s (cf.prec cg) f g Df Dg l0,
    have IH₁ : _ := @evaln_use (s+1) cf f g Df Dg h,
    have IH₂ : _ := @evaln_use (s+1) cg f g Df Dg h,
    funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀, IH₁, IH₂] }
| (s+1) (rfind' cf)  f g Df Dg := λ h, 
    have l0 : ∀ (x : ℕ), x < s → f x = g x := λ x e, h x (nat.lt.step e),
    have IH₀ : _ := @evaln_use (s+1) cf f g Df Dg h,
    have IH₁ : _ := @evaln_use s cf.rfind' f g Df Dg l0,
    funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀, IH₁] }

theorem evaln_use' {s} {f g : ℕ →. ℕ} [∀ x, decidable (f x).dom] [∀ x, decidable (g x).dom]
  (h : ∀ x, x < s → f x = g x) :
  evaln s f = evaln s g := 
funext $ λ c, evaln_use h

theorem evaln_bound {f : ℕ →. ℕ} [∀ x, decidable (f x).dom] : ∀ {k c n x}, x ∈ evaln k f c n → n < k
| 0     c n x h := by simp [evaln] at h; cases h
| (k+1) c n x h := begin
  suffices : ∀ {o : option ℕ}, x ∈ guard (n ≤ k) >> o → n < k + 1,
  { cases c; rw [evaln] at h; try { exact this h } },
  simpa [(>>)] using nat.lt_succ_of_le
end

theorem evaln_bound_none {f : ℕ →. ℕ} [∀ x, decidable (f x).dom] {k c n} (h : k ≤ n) : evaln k f c n = none :=
by { cases e : evaln k f c n with v; simp,
     have := evaln_bound e, exact nat.lt_le_antisymm this h }

theorem evaln_mono : ∀ {s₁ s₂ : ℕ} {c : code} {f : ℕ →. ℕ} [∀ x, decidable (f x).dom] {n x : ℕ},
  by exactI s₁ ≤ s₂ → evaln s₁ f c n = some x → evaln s₂ f c n = some x
| 0      _      _            _ _ _ _ := λ _ h, by simp [evaln] at h; cases h
| (s₀+1) 0      _            _ _ _ _ := λ e h, by exfalso; exact nat.not_succ_le_zero s₀ e
| (s₀+1) (s₁+1) oracle       f _ n x := λ hs,
    by { simp[evaln], have : n ≤ s₀ ∨ ¬ n ≤ s₀, omega,
         cases this; simp[(>>), this], exact λ e, ⟨by omega, e⟩,
         intros _ c, exfalso, exact option.not_mem_none _ c }
| (s₀+1) (s₁+1) zero         f _ n x := λ hs, 
    by simp[evaln, (>>)]; exact λ _ e, ⟨by omega, e⟩
| (s₀+1) (s₁+1) succ         f _ n x := λ hs, 
    by simp[evaln, (>>)]; exact λ _ e, ⟨by omega, e⟩
| (s₀+1) (s₁+1) left         f _ n x := λ hs, 
    by simp[evaln, (>>)]; exact λ _ e, ⟨by omega, e⟩
| (s₀+1) (s₁+1) right        f _ n x := λ hs, 
    by simp[evaln, (>>)]; exact λ _ e, ⟨by omega, e⟩
| (s₀+1) (s₁+1) (pair cf cg) f D n x := λ hs,
    have IH₀ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f D n y hs,
    have IH₁ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cg f D n y hs,
    by { simp[evaln, (>>)], assume e0 ex,
         have : ∃ y, by exactI evaln (s₀ + 1) f cf n = some y,
         { cases (by exactI evaln (s₀ + 1) f cf n); simp[(<*>)] at ex ⊢, { exact ex } },
         rcases this with ⟨y₀, hy₀⟩,
         have : ∃ y, by exactI evaln (s₀ + 1) f cg n = some y,
         { cases (by exactI evaln (s₀ + 1) f cg n); simp[(<*>)] at ex ⊢, exact ex },         
         rcases this with ⟨y₁, hy₁⟩,
         simp[hy₀, hy₁, IH₀ _ _ hy₀, IH₁ _ _ hy₁] at ex ⊢,
         exact ⟨le_trans e0 (nat.le_of_succ_le_succ hs), ex⟩ }
| (s₀+1) (s₁+1) (comp cf cg) f D n x := λ hs,        
    have IH₀ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f D n y hs,
    have IH₁ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cg f D n y hs,
    by { simp[evaln, (>>)], assume e0 y ey ex,
         refine ⟨le_trans e0 (nat.le_of_succ_le_succ hs), y, IH₁ _ _ ey, IH₀ _ _ ex⟩ }
| (s₀+1) (s₁+1) (prec cf cg) f D n x := λ hs,
    have IH₀ : _ := λ n y, @evaln_mono s₀ s₁ (cf.prec cg) f D n y (nat.le_of_succ_le_succ hs),
    have IH₁ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f D n y hs,
    have IH₂ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cg f D n y hs,
    by { simp[evaln, (>>)],
         cases n.unpair.snd with n0; simp,
         assume e0 ex,
         exact ⟨le_trans e0 (nat.le_of_succ_le_succ hs), IH₁ _ _ ex⟩,
         assume e0 y ey ex,
         refine ⟨le_trans e0 (nat.le_of_succ_le_succ hs), y, IH₀ _ _ ey, IH₂ _ _ ex⟩ }
| (s₀+1) (s₁+1) (rfind' cf)  f D n x := λ hs,
    have IH₀ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f D n y hs,
    have IH₁ : _ := λ n y, @evaln_mono s₀ s₁ cf.rfind' f D n y (nat.le_of_succ_le_succ hs),
    by { simp[evaln, (>>), pure],
         assume e0 y ey ex,
         refine ⟨by omega, y, IH₀ _ _ ey, _⟩,
         cases y with y0; simp at ex ⊢, exact ex, exact IH₁ _ _ ex }

def eval (f : ℕ →. ℕ) : code → ℕ →. ℕ 
| oracle       := λ n, f n
| zero         := pure 0
| succ         := nat.succ
| left         := ↑(λ n : ℕ, n.unpair.1)
| right        := ↑(λ n : ℕ, n.unpair.2)
| (pair cf cg) := λ n, mkpair <$> eval cf n <*> eval cg n
| (comp cf cg) := λ n, eval cg n >>= eval cf
| (prec cf cg) := nat.unpaired (λ a n,
    n.elim (eval cf a) (λ y IH, do i ← IH, eval cg (mkpair a (mkpair y i))))
| (rfind' cf) := nat.unpaired (λ a m,
    (nat.rfind (λ n, (λ m, m = 0) <$>
      eval cf (mkpair a (n + m)))).map (+ m))

theorem evaln_sound {f : ℕ →. ℕ} [∀ x, decidable (f x).dom] : ∀ {s c n x},
  x ∈ evaln s f c n → x ∈ eval f c n
| 0     _ _ _ h := by simp [evaln] at h; cases h
| (s + 1) oracle n x h := by { simp [eval, evaln, (>>)] at h ⊢, exact h.2 }
| (s + 1) zero   n x h := 
    by { simp [eval, evaln, (>>), pure, pfun.pure] at h ⊢, exact eq.symm h.2 }
| (s + 1) succ   n x h := 
    by { simp [eval, evaln, (>>), pure, pfun.pure] at h ⊢, exact eq.symm h.2 }
| (s + 1) left   n x h := 
    by { simp [eval, evaln, (>>), pure, pfun.pure] at h ⊢, exact eq.symm h.2 }
| (s + 1) right   n x h := 
    by { simp [eval, evaln, (>>), pure, pfun.pure] at h ⊢, exact eq.symm h.2 }
| (s + 1) (pair cf cg) n x h :=
    have IH₀ : _ := @evaln_sound (s + 1) cf,
    have IH₁ : _ := @evaln_sound (s + 1) cg,
    by{ simp [eval, evaln, (>>), (<*>)] at h ⊢, 
        rcases h with ⟨_, y, hy, z, hz, ex⟩,
        refine ⟨y, IH₀ hy, z, IH₁ hz, ex⟩ }
| (s + 1) (comp cf cg) n x h :=
    have IH₀ : _ := @evaln_sound (s + 1) cf,
    have IH₁ : _ := @evaln_sound (s + 1) cg,
    by{ simp [eval, evaln, (>>), (<*>)] at h ⊢, 
        rcases h with ⟨_, y, hy, hz⟩,
        refine ⟨y, IH₁ hy, IH₀ hz⟩ }
| (s + 1) (prec cf cg) n x h :=
    have IH₀ : _ := @evaln_sound (s + 1) cf,
    have IH₁ : _ := @evaln_sound (s + 1) cg,
    by{ simp [eval, evaln, (>>)] at h ⊢,
        rcases h with ⟨_, hx⟩, revert hx,
        induction n.unpair.2 with m IH generalizing x; simp,
        { exact IH₀ },
        { refine λ y h₁ h₂, ⟨y, IH _ _, _⟩,
          { have := evaln_mono s.le_succ h₁,
        simp [evaln, (>>)] at this,
        exact this.2 },
        { exact IH₁ h₂ } } }
| (s + 1) (rfind' cf) n x h :=
    have IH₀ : _ := @evaln_sound (s+1) cf,
    have IH₁ : _ := @evaln_sound s cf.rfind',
  begin
    simp [eval, evaln, (>>)] at h ⊢,
    rcases h with ⟨_, m, hm, h⟩,
    cases e : m with m0; simp[e, pure] at hm h,
    { refine ⟨0, ⟨by simp; exact IH₀ hm, by simp⟩, by simp[h]⟩ },
    { have := IH₁ h,  simp[eval] at this,
      rcases this with ⟨y, ⟨hc0, hc1⟩, ex⟩,
      refine ⟨y+1, ⟨
        by simpa [add_comm, add_left_comm] using hc0, λ b eb, _⟩, 
        by simpa [add_comm, add_left_comm] using ex⟩,
      { cases b with b0, refine ⟨m0 + 1, by simp; exact IH₀ hm, by simp⟩, 
        have : b0.succ + n.unpair.snd = b0 + (n.unpair.snd + 1), omega,
        rw this, exact hc1 (nat.lt_of_succ_lt_succ eb) } }
  end

theorem evaln_complete {f : ℕ →. ℕ} [∀ x, decidable (f x).dom] {c n x} :
  x ∈ eval (λ x, f x) c n ↔ ∃ k, x ∈ evaln k f c n := ⟨λ h,
begin
  suffices : ∃ k, x ∈ evaln (k+1) f c n,
  { exact let ⟨k, h⟩ := this in ⟨k+1, h⟩ },
    induction c generalizing n x;
    simp [eval, evaln, pure, pfun.pure, (<*>), (>>)] at h ⊢,
    { exact ⟨⟨n, by refl⟩, h⟩ },
    { use n, have : min n n.unpair.fst.unpair.fst = n.unpair.fst.unpair.fst,
      { simp, exact le_trans (nat.unpair_left_le _) (nat.unpair_left_le _) }, simp [this,h] },
    { exact ⟨⟨_, le_refl _⟩, h.symm⟩ },
    { exact ⟨⟨_, le_refl _⟩, h.symm⟩ },
    { exact ⟨⟨_, le_refl _⟩, h.symm⟩ },
    case nat.rpartrec.code.pair : cf cg hf hg 
    { rcases h with ⟨x, hx, y, hy, rfl⟩,
      rcases hf hx with ⟨k₁, hk₁⟩, rcases hg hy with ⟨k₂, hk₂⟩,
      refine ⟨max k₁ k₂, le_max_of_le_left $ nat.le_of_lt_succ $ evaln_bound hk₁, x, _, y, _, rfl⟩,
      exact evaln_mono (nat.succ_le_succ $ le_max_left _ _) hk₁, 
      exact evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk₂ },
    case nat.rpartrec.code.comp : cf cg hf hg 
    { rcases h with ⟨y, hy, hx⟩,
      rcases hf hx with ⟨k₁, hk₁⟩, rcases hg hy with ⟨k₂, hk₂⟩,
      refine ⟨max k₂ k₁, le_max_of_le_left $ nat.le_of_lt_succ $ evaln_bound hk₂, y, _, _⟩,
      exact evaln_mono (nat.succ_le_succ $ le_max_left _ _) hk₂,
      exact evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk₁ },
    case nat.rpartrec.code.prec : cf cg hf hg
    { revert h,
      generalize : n.unpair.1 = n₁, generalize : n.unpair.2 = n₂,
      induction n₂ with m IH generalizing x n; simp,
      { intro, rcases hf h with ⟨k, hk⟩,
        exact ⟨_, le_max_left _ _,
          evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk⟩ },
      { intros y hy hx,
        rcases IH hy with ⟨k₁, nk₁, hk₁⟩, rcases hg hx with ⟨k₂, hk₂⟩,
        refine ⟨(max k₁ k₂).succ, nat.le_succ_of_le $ le_max_of_le_left $
          le_trans (le_max_left _ (mkpair n₁ m)) nk₁, y,
          evaln_mono (nat.succ_le_succ $ le_max_left _ _) _,
          evaln_mono (nat.succ_le_succ $ nat.le_succ_of_le $ le_max_right _ _) hk₂⟩,
        simp [evaln, (>>)],
        exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩ } },
    case nat.rpartrec.code.rfind' : cf hf
    { rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩,
      suffices : ∃ k, y + n.unpair.2 ∈ evaln (k+1) f (rfind' cf)
        (mkpair n.unpair.1 n.unpair.2), {simpa [evaln, (>>)]},
      revert hy₁ hy₂, generalize : n.unpair.2 = m, intros,
      induction y with y IH generalizing m; simp [evaln, (>>)],
      { simp at hy₁, rcases hf hy₁ with ⟨k, hk⟩,
        exact ⟨_, nat.le_of_lt_succ $ evaln_bound hk, _, hk, by simp; refl⟩ },
      { rcases hy₂ (nat.succ_pos _) with ⟨a, ha, a0⟩,
        rcases hf ha with ⟨k₁, hk₁⟩,
        rcases IH m.succ
            (by simpa [nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
            (λ i hi, by simpa [nat.succ_eq_add_one, add_comm, add_left_comm] using
              hy₂ (nat.succ_lt_succ hi))
          with ⟨k₂, hk₂⟩,
        use (max k₁ k₂).succ,
        rw [zero_add] at hk₁,
        use (nat.le_succ_of_le $ le_max_of_le_left $ nat.le_of_lt_succ $ evaln_bound hk₁),
        use a,
        use evaln_mono (nat.succ_le_succ $ nat.le_succ_of_le $ le_max_left _ _) hk₁,
        simpa [nat.succ_eq_add_one, a0, -max_eq_left, -max_eq_right, add_comm, add_left_comm] using
            evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk₂ } },
end, λ ⟨k, h⟩, evaln_sound h⟩

theorem evaln_complete_dec {c : code} {f : ℕ →. ℕ} [∀ x, decidable (f x).dom] [D : decidable_pred (eval f c).dom] : ∀ m, ∃ s₀,
  ∀ n a, n < m → eval f c n = some a → evaln s₀ f c n = some a := λ m,
begin
  induction m with m0 ih, simp,
  rcases ih with ⟨s₀, hs₀⟩,
  have e : eval f c m0 = none ∨ ∃ v, eval f c m0 = some v := eq_none_or_eq_some (eval f c m0),
  cases e,
  { refine ⟨s₀, λ n a en ha, _⟩,
    have : n < m0 ∨ n = m0, from nat.lt_succ_iff_lt_or_eq.mp en,
    cases this, { exact hs₀ _ _ this ha },
    { exfalso, rw this at ha, rw e at ha, exact part.some_ne_none _ (eq.symm ha) } },
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
      have : a = v, from part.some_inj.mp (by simp only [←e, ←ha, en']),
      show evaln (max s₀ s₁) f c m0 = option.some a, rw this,
        from evaln_mono (le_max_right s₀ s₁) hs₁ } }
end

theorem eval_inclusion {c x y} {f : ℕ →. ℕ} [∀ x, decidable (f x).dom] (h : y ∈ eval f c x) :
  ∃ s, ∀ {g : ℕ →.ℕ} [∀ x, decidable (g x).dom],
  (∀ x y, x < s → y ∈ f x → y ∈ g x) → y ∈ eval g c x :=
by { have : ∃ s, y ∈ evaln s f c x := evaln_complete.mp h, rcases this with ⟨s, hs⟩,
     refine ⟨s, λ g D h, by exactI evaln_complete.mpr ⟨s, evaln_inclusion h hs⟩⟩ }

@[simp] theorem evaln_const (s : ℕ) (f : ℕ →. ℕ) [∀ x, decidable (f x).dom] :
  ∀ n m, evaln (s+1) f (code.const n) m = guard (n ≤ s+1) >> guard (m ≤ s) >> option.some n
| 0     m := by { simp[code.const, evaln, (>>), pure], }
| (n+1) m := have IH : _ := evaln_const n m, 
  by { simp [code.const, evaln, IH, pure, (>>)],
    by_cases e1 : n ≤ s; simp[e1, failure, alternative.failure],
    by_cases e2 : m ≤ s; simp[e1, e2, failure, alternative.failure],
    refine ⟨n, ⟨⟨(le_add_right e1), (), rfl⟩, rfl⟩, e1, rfl⟩ }

@[simp] theorem eval_const (f : ℕ →. ℕ) : ∀ n m, eval f (code.const n) m = part.some n
| 0     m := rfl
| (n+1) m := by simp! *

@[simp] theorem eval_id (f : ℕ →. ℕ) (n) : eval f code.id n = part.some n := by simp! [(<*>)]

@[simp] theorem eval_curry (f : ℕ →. ℕ) (c n x) :
  eval f (curry c n) x = eval f c (mkpair n x) :=
by simp! [(<*>)]

--@[simp] theorem eval_ctrans (f c₁ c₂ x) : eval (eval f c₁) c₂ x = eval f (ctrans c₁ c₂) x :=
--by simp! [(<*>)]

@[simp] theorem evaln_curry (s : ℕ) (f : ℕ →. ℕ) [∀ x, decidable (f x).dom] (c : code) (n x : ℕ) :
  evaln s f (curry c n) x = evaln s f c (n.mkpair x) :=
begin
  cases s, simp,
  simp [curry, evaln], 
  by_cases e0 : x ≤ s; simp [code.id, evaln, e0, pure, (>>), failure, alternative.failure],
  by_cases e1 : n ≤ s+1; simp [e0, e1, pure, (>>), (<*>), failure, alternative.failure],
  { cases e : evaln (s + 1) f c (n.mkpair x) with y; simp,
    have : n.mkpair x < s + 1, from evaln_bound e,
    have : n ≤ s + 1, from le_of_lt 
      (gt_of_gt_of_ge this (nat.left_le_mkpair n x)),
    contradiction },
  { cases e : evaln (s + 1) f c (n.mkpair x) with y; simp,
    have : n.mkpair x ≤ s := nat.lt_succ_iff.mp (evaln_bound e),
    have : x ≤ s := le_trans (nat.right_le_mkpair _ _) this,
    contradiction }
end

section
open primrec

theorem pair_prim : primrec₂ pair :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit0.comp $ nat_bit0.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 5)

theorem comp_prim : primrec₂ comp :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit0.comp $ nat_bit1.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 5)

theorem prec_prim : primrec₂ prec :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit1.comp $ nat_bit0.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 5)

theorem rfind_prim : primrec rfind' :=
of_nat_iff.2 $ encode_iff.1 $ nat_add.comp
  (nat_bit1.comp $ nat_bit1.comp $
    encode_iff.2 $ primrec.of_nat code)
  (const 5)

theorem const_prim : primrec code.const :=
(primrec.id.nat_iterate (primrec.const zero)
  (comp_prim.comp (primrec.const succ) primrec.snd).to₂).of_eq $
λ n, by simp; induction n; simp [*, code.const, function.iterate_succ']

theorem curry_prim : primrec₂ curry :=
comp_prim.comp primrec.fst $
pair_prim.comp (const_prim.comp primrec.snd) (primrec.const code.id)

end

theorem rpartrec_rfind' {f} : nat.rpartrec f (nat.unpaired (λ a m,
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
  have := (rpartrec.rfind (c₂.map c₁.to_rcomp.to₂).to₂).map c₀.to_rcomp.to₂,
  simp at this,
  exact this.comp primrec.unpair.to_rcomp
end

theorem exists_code {f g : ℕ →. ℕ} [D : ∀ x, decidable (g x).dom] :
  nat.rpartrec g f ↔ ∃ c, eval g c = f := ⟨λ h,
begin
  induction h,
  case nat.rpartrec.oracle 
  { exact ⟨oracle, by { simp[eval] }⟩ },  
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
    simp [eval, (<*>), pure, pfun.pure, part.map_id'],  },
end,λ h, begin
  rcases h with ⟨c, rfl⟩, induction c,
  case nat.rpartrec.code.oracle 
  { simp[eval], exact nat.rpartrec.oracle },
  case nat.rpartrec.code.zero { exact nat.rpartrec.zero },
  case nat.rpartrec.code.succ { exact nat.rpartrec.succ },
  case nat.rpartrec.code.left { exact nat.rpartrec.left },
  case nat.rpartrec.code.right { exact nat.rpartrec.right },
  case nat.rpartrec.code.pair : cf cg pf pg { exact pf.pair pg },
  case nat.rpartrec.code.comp : cf cg pf pg { exact pf.comp pg },
  case nat.rpartrec.code.prec : cf cg pf pg { exact pf.prec pg },
  case nat.rpartrec.code.rfind' : cf pf { exact nat.rpartrec.trans rpartrec_rfind' pf },
end⟩

end nat.rpartrec.code
open nat.rpartrec 

variables {α : Type*} {σ : Type*} {β : Type*} {τ : Type*} {γ : Type*} {μ : Type*} 
variables [primcodable α] [primcodable σ] [primcodable β] [primcodable τ] [primcodable γ] [primcodable μ]

def pfun_to_nat (f : β →. τ) : ℕ →. ℕ := λ n, part.bind(decode β n) (λ a, (f a).map encode)

instance decidable_pfun_to_nat_dom
  (f : β →. τ) [D : ∀ x, decidable (f x).dom] : ∀ x, decidable (pfun_to_nat f x).dom :=
by { intros n,
    cases C₁ : decode β n with x; simp[pfun_to_nat, C₁], { simp[part.none], exact decidable.false },
    { exact D x } }

def univn (α σ) [primcodable α] [primcodable σ] (s : ℕ) (f : β →. τ) [D : ∀ x, decidable (f x).dom] (e : ℕ) :
  α → option σ :=
(λ a, (code.evaln s (pfun_to_nat f) (of_nat code e) (encode a)).bind (λ x, (decode σ x)))

notation `⟦`e`⟧*`f:max` [`s`]` := univn _ _ s f e
notation `⟦`e`⟧^`f:max` [`s`]` := univn _ _ s ↑ᵣf e

def univ (α σ) [primcodable α] [primcodable σ] (f : β →. τ) (e : ℕ) : α →. σ := (λ a,
(code.eval (pfun_to_nat f) (of_nat code e) (encode a)).bind (λ x, (decode σ x)))

notation `⟦`e`⟧*`f:max := univ _ _ f e
notation `⟦`e`⟧^`f:max := univ _ _ ↑ᵣf e

notation `⟦`e`⟧ᵪ*`f:max` [`s`]` := univn ℕ bool s f e
notation `⟦`e`⟧ₙ*`f:max` [`s`]` := univn ℕ ℕ s f e
notation `⟦`e`⟧ᵪ*`f:max := univ ℕ bool f e
notation `⟦`e`⟧ₙ*`f:max := univ ℕ ℕ f e

notation `⟦`e`⟧ᵪ^`f:max` [`s`]` := univn ℕ bool s ↑ᵣf e
notation `⟦`e`⟧ₙ^`f:max` [`s`]` := univn ℕ ℕ s ↑ᵣf e
notation `⟦`e`⟧ᵪ^`f:max := univ ℕ bool ↑ᵣf e
notation `⟦`e`⟧ₙ^`f:max := univ ℕ ℕ ↑ᵣf e

def univn0 (α σ) [primcodable α] [primcodable σ] (s : ℕ) (e : ℕ) : α → option σ :=
univn α σ s partrec_fun e

def univ0 (α σ) [primcodable α] [primcodable σ] (e : ℕ) : α →. σ :=
univ α σ partrec_fun e

notation `⟦`e`⟧⁰`:max` [`s`]` := univn0 _ _ s e
notation `⟦`e`⟧⁰`:max := univ0 _ _ e

def re_set (α σ) [primcodable α] [primcodable σ] (p : β →. τ) (e : ℕ) : set α :=
{x | (⟦e⟧*p x : part σ).dom}

def re_set0 (α σ) [primcodable α] [primcodable σ] (e : ℕ) : set α :=
{x | (univ0 α σ e x : part σ).dom}

notation `W⟦`e`⟧^`f:max := re_set _ _ ↑ₒf e

notation `W⟦`e`⟧ᵪ^`f:max := re_set ℕ bool ↑ₒf e
notation `W⟦`e`⟧ₙ^`f:max := re_set ℕ ℕ ↑ₒf e
notation `W⟦`e`⟧ᵪ⁰`:max := re_set0 ℕ bool e
notation `W⟦`e`⟧ₙ⁰`:max := re_set0 ℕ ℕ e

def curry {α} [primcodable α] (e : ℕ) (n : α) : ℕ := encode (code.curry (of_nat _ e) (encode n))

-- smn定理
@[simp] theorem eval_curry (f : γ →. τ) (e : ℕ) (n : β) (x : α) :
  (⟦curry e n⟧*f x : part σ) = (⟦e⟧*f (n, x) : part σ) :=
by simp[curry, univ]

namespace rpartrec

theorem curry_prim {α} [primcodable α] : primrec₂ (@curry α _) :=
(primrec.encode.comp $ code.curry_prim.comp 
  ((primrec.of_nat code).comp primrec.fst) ((@primrec.encode α _).comp primrec.snd))

open primrec

theorem univn_sound {e} {p : β →. τ} [∀ x, decidable (p x).dom] {x : α} {y : σ} {s : ℕ} :
  y ∈ (⟦e⟧*p [s] x : option σ) → y ∈ (⟦e⟧*p x : part σ) :=
begin
  simp[univn, univ], intros s' h eqn, 
  exact ⟨s', code.evaln_sound h, eqn⟩
end

theorem univn_complete {p : β →. τ} [D : ∀ x, decidable (p x).dom] {e x} {n : α} :
  x ∈ (⟦e⟧*p n : part σ) ↔ ∃ s, ⟦e⟧*p [s] n = some x :=
begin
  simp[univn, univ], split,
  { rintros ⟨a, ha, ea⟩,
    have : ∀ x, decidable (part.bind (decode β x) (λ a, part.map encode (p a))).dom,
      from decidable_pfun_to_nat_dom _,
    rcases by exactI code.evaln_complete.mp ha with ⟨s, hs⟩,
    refine ⟨s, a, cast (by congr) hs, ea⟩ },
  { rintros ⟨s, a, ha, ea⟩,
    have := code.evaln_complete.mpr ⟨s, ha⟩,
    refine ⟨a, this, ea⟩ }
end

theorem univn_dom_complete {p : β →. τ} [∀ x, decidable (p x).dom] {e} {n : α} :
  (⟦e⟧*p n : part σ).dom ↔ ∃ s, (⟦e⟧*p [s] n : option σ).is_some :=
begin
  simp[part.dom_iff_mem, option.is_some_iff_exists], split,
  { rintros ⟨y, h⟩, rcases univn_complete.mp h with ⟨s, h⟩, refine ⟨s, y, h⟩ },
  { rintros ⟨s, y, h⟩, have := univn_complete.mpr ⟨s, h⟩, refine ⟨y, this⟩ }
end

theorem univn_mono {e} {p : β →. τ} [∀ x, decidable (p x).dom] {s₀ s₁ : ℕ} {x : α} {y : σ}
  (eqn : s₀ ≤ s₁) : ⟦e⟧*p [s₀] x = some y → ⟦e⟧*p [s₁] x = some y :=
by { simp [univn], intros z h eqn_z,
     refine ⟨z, code.evaln_mono eqn h, eqn_z⟩ }

theorem univn_dom_mono {e} {p : β →. τ} [∀ x, decidable (p x).dom] {s₀ s₁ : ℕ} {x : α}
  (eqn : s₀ ≤ s₁) : (⟦e⟧*p [s₀] x : option σ).is_some → (⟦e⟧*p [s₁] x : option σ).is_some :=
begin
  cases C : (⟦e⟧*p [s₀] x : option σ) with y; simp,
  simp[univn_mono eqn C]
end

theorem univn_mono_eq {e} {p : β →. τ} [∀ x, decidable (p x).dom] {s₀ s₁ : ℕ} {x : α} {y₀ y₁ : σ}
  (h₀ : ⟦e⟧*p [s₀] x = some y₀) (h₁ : ⟦e⟧*p [s₁] x = some y₁) : y₀ = y₁ :=
begin
  have : s₀ ≤ s₁ ∨ s₁ ≤ s₀, from le_total _ _,
  cases this,
  { have := univn_mono this h₀, simp [this] at h₁, exact h₁ },
  { have := univn_mono this h₁, simp [this] at h₀, exact eq.symm h₀ }
end 

theorem univn_use {s e} {p q : ℕ →. β} [∀ x, decidable (p x).dom] [∀ x, decidable (q x).dom]
  (h : ∀ x, x < s → p x = q x) : (⟦e⟧*p [s] : α → option σ) = ⟦e⟧*q [s] :=
begin
  simp [univn],
  suffices :
    code.evaln s (pfun_to_nat p) (of_nat code e) =
    code.evaln s (pfun_to_nat q) (of_nat code e),
  { funext, rw this },
  apply code.evaln_use, intros u eqn, simp[pfun_to_nat], congr, exact h _ eqn
end

theorem univn_tot_use {s e} {f g : ℕ → β}
  (h : ∀ x, x < s → f x = g x) : (⟦e⟧^f [s] : α → option σ) = ⟦e⟧^g [s] :=
univn_use (λ x lt, by simp[h x lt])

theorem univn_mono_use
  {e} {p q : ℕ →. τ} [∀ x, decidable (p x).dom] [∀ x, decidable (q x).dom] {s₀ s₁ : ℕ} {x : α} {y : σ}
  (h : ∀ x < s₀, p x = q x) (eqn : s₀ ≤ s₁) : ⟦e⟧*p [s₀] x = some y → ⟦e⟧*q [s₁] x = some y := λ eq_y,
  have (⟦e⟧*p [s₀] x : option σ) = ⟦e⟧*q [s₀] x, from congr_fun (univn_use h) x,  
univn_mono eqn (by simp[←this, eq_y])

theorem univn_tot_mono_use {e} {f g : ℕ → τ} {s₀ s₁ : ℕ} {x : α} {y : σ}
  (h : ∀ x < s₀, f x = g x) (eqn : s₀ ≤ s₁) : ⟦e⟧^f [s₀] x = some y → ⟦e⟧^g [s₁] x = some y :=
univn_mono_use (by simp; exact h) eqn

theorem eval_inclusion {e} {x : α} {y : σ} {p : ℕ →. τ} [∀ x, decidable (p x).dom]
  (h : y ∈ (⟦e⟧*p x : part σ)) : ∃ s, ∀ {q : ℕ →. τ} [∀ x, decidable (q x).dom],
  (∀ x y, x < s → y ∈ p x → y ∈ q x) → y ∈ (⟦e⟧*q x : part σ) := 
by { simp [part.eq_some_iff, univ] at h ⊢, rcases h with ⟨a, h, e⟩,
     rcases nat.rpartrec.code.eval_inclusion h with ⟨s, hs⟩,
     refine ⟨s, λ q D h, ⟨a, by exactI hs (λ x y e ey,
       (by {show y ∈ pfun_to_nat q x,
            simp[pfun_to_nat] at ey ⊢, rcases ey with ⟨z, mem_p, eq⟩,
            refine ⟨z, h _ _ e mem_p, eq⟩, })), e⟩⟩ }

theorem eval_inclusion_tot {e} {x : α} {y : σ}
  {f : ℕ → τ} (h : y ∈ (⟦e⟧^f x : part σ)) : ∃ s, ∀ {g : ℕ → τ},
  (∀ x y, x < s → f x = y → g x = y) → y ∈ (⟦e⟧^g x : part σ) := 
by { rcases eval_inclusion h with ⟨s, hs⟩, refine ⟨s, λ g hfg, hs _⟩,
     simp, intros x y lt eq_y, exact eq.symm (hfg x y lt (eq.symm eq_y)) }

end rpartrec

theorem rcomputable.curry {α} [primcodable α] {σ : Type*} {τ : Type*} [primcodable σ] [primcodable τ]
  {o : σ →. τ} : (@curry α _) computable₂_in o := rpartrec.curry_prim.to_rcomp