import computability.partrec
import computability.partrec_code
import data.pfun
import tactic

open encodable denumerable roption

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
| univn  : code → code

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

def encode_code : code → ℕ
| oracle       := 0
| zero         := 1
| succ         := 2
| left         := 3
| right        := 4
| (pair cf cg) := (bit0 $ bit0 $ bit0 (mkpair (encode_code cf) (encode_code cg))) + 5
| (comp cf cg) := (bit0 $ bit0 $ bit1 (mkpair (encode_code cf) (encode_code cg))) + 5
| (prec cf cg) := (bit0 $ bit1 $ bit0 (mkpair (encode_code cf) (encode_code cg))) + 5
| (rfind' cf)  := (bit0 $ bit1 $ bit1 (encode_code cf)) + 5
| (univn cf)   := (bit1 (encode_code cf)) + 5

lemma guygk (n) : n ≤ n+9 := nat.le.intro rfl

def of_nat_code : ℕ → code
| 0 := oracle
| 1 := zero
| 2 := succ
| 3 := left
| 4 := right
| (e+5) :=
  have div8 : e.div2.div2.div2 ≤ e :=
    by { simp[nat.div2_val], 
         exact le_trans (nat.div_le_self (e/2/2) 2) 
         (le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2)) },
  have e.div2.div2.div2 < e + 5 := nat.lt_succ_iff.mpr (le_trans div8 (nat.le.intro rfl)),
  have e.div2.div2.div2.unpair.1 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_le_left _) div8) (nat.le.intro rfl)),
  have e.div2.div2.div2.unpair.2 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_le_right _) div8) (nat.le.intro rfl)),
  have e.div2 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (by simp[nat.div2_val]; exact nat.div_le_self _ _) (nat.le.intro rfl)),
  match e.bodd, e.div2.bodd, e.div2.div2.bodd with
  | ff, ff, ff := pair (of_nat_code e.div2.div2.div2.unpair.1)
                        (of_nat_code e.div2.div2.div2.unpair.2)
  | ff, ff, tt := comp (of_nat_code e.div2.div2.div2.unpair.1)
                        (of_nat_code e.div2.div2.div2.unpair.2)
  | ff, tt, ff := prec (of_nat_code e.div2.div2.div2.unpair.1)
                        (of_nat_code e.div2.div2.div2.unpair.2)
  | ff, tt, tt := rfind' (of_nat_code e.div2.div2.div2)
  | tt, _,  _  := univn (of_nat_code e.div2)
end

private lemma encode_of_nat_code : ∀ e, encode_code (of_nat_code e) = e
| 0     := rfl
| 1     := rfl
| 2     := rfl
| 3     := rfl
| 4     := rfl
| (e+5) :=
  have div8 : e.div2.div2.div2 ≤ e :=
    by { simp[nat.div2_val], 
         exact le_trans (nat.div_le_self (e/2/2) 2) 
         (le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2)) },
  have e.div2.div2.div2 < e + 5 := nat.lt_succ_iff.mpr (le_trans div8 (nat.le.intro rfl)),
  have e.div2.div2.div2.unpair.1 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_le_left _) div8) (nat.le.intro rfl)),
  have e.div2.div2.div2.unpair.2 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_le_right _) div8) (nat.le.intro rfl)),
  have e.div2 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (by simp[nat.div2_val]; exact nat.div_le_self _ _) (nat.le.intro rfl)),
  have IH₀ : _ := encode_of_nat_code e.div2.div2.div2,
  have IH₁ : _ := encode_of_nat_code e.div2.div2.div2.unpair.1,
  have IH₂ : _ := encode_of_nat_code e.div2.div2.div2.unpair.2,
  have IH₃ : _ := encode_of_nat_code e.div2,
  begin
    suffices :
      (of_nat_code (e + 5)).encode_code =
      nat.bit e.bodd (nat.bit e.div2.bodd (nat.bit e.div2.div2.bodd e.div2.div2.div2)) + 5,
    { simp[nat.bit_decomp, this] },
    simp [encode_code, of_nat_code],
    cases e.bodd; simp [encode_code, of_nat_code, nat.bit, IH₀, IH₁, IH₂],
    cases e.div2.bodd; cases e.div2.div2.bodd;
    simp [encode_code, of_nat_code, nat.bit, IH₀, IH₁, IH₂],
    { have h : ∀ m : ℕ, cond m.bodd bit1 bit0 m.div2 = m,
      { intros m, exact nat.bit_decomp m }, simp[h, IH₃] }
  end

private lemma of_nat_code_encode : ∀ c, of_nat_code (encode_code c) = c
| oracle       := rfl
| zero         := rfl
| succ         := rfl
| left         := rfl
| right        := rfl
| (pair cf cg) := by { simp[encode_code, of_nat_code],
    exact ⟨of_nat_code_encode cf, of_nat_code_encode cg⟩ }
| (comp cf cg) := by { simp[encode_code, of_nat_code],
    exact ⟨of_nat_code_encode cf, of_nat_code_encode cg⟩ }
| (prec cf cg) := by { simp[encode_code, of_nat_code],
    exact ⟨of_nat_code_encode cf, of_nat_code_encode cg⟩ }
| (rfind' cf)  := by { simp[encode_code, of_nat_code],
    exact of_nat_code_encode cf }
| (univn cf)   := by { simp[encode_code, of_nat_code],
    exact of_nat_code_encode cf }

instance : denumerable code :=
mk' ⟨encode_code, of_nat_code,
  of_nat_code_encode,
  encode_of_nat_code⟩

def evaln : ℕ → (ℕ → option ℕ) → code → ℕ → option ℕ
| 0     f _            := λ _, none
| (s+1) f oracle       := λ n, guard (n ≤ s) >> f n
| (s+1) f zero         := λ n, guard (n ≤ s) >> pure 0
| (s+1) f succ         := λ n, guard (n ≤ s) >> pure (nat.succ n)
| (s+1) f left         := λ n, guard (n ≤ s) >> pure n.unpair.1
| (s+1) f right        := λ n, guard (n ≤ s) >> pure n.unpair.2
| (s+1) f (pair cf cg) := λ n, guard (n ≤ s) >>
    mkpair <$> evaln (s+1) f cf n <*> evaln (s+1) f cg n
| (s+1) f (comp cf cg) := λ n, guard (n ≤ s) >>
    do x ← evaln (s+1) f cg n, evaln (s+1) f cf x
| (s+1) f (prec cf cg) := λ n, guard (n ≤ s) >>
    n.unpaired (λ a n,
    n.cases (evaln (s+1) f cf a) $ λ y, do
    i ← evaln s f (prec cf cg) (mkpair a y),
    evaln (s+1) f cg (mkpair a (mkpair y i)))
| (s+1) f (rfind' cf)  := λ n, guard (n ≤ s) >>
    n.unpaired (λ a m, do
    x ← evaln (s+1) f cf (mkpair a m),
    if x = 0 then pure m else
    evaln s f (rfind' cf) (mkpair a (m+1)))
| (s+1) f (univn cf)       := λ n, guard (n ≤ s) >> 
    evaln (min s n.unpair.1.unpair.1)
    (evaln (s+1) f cf) (of_nat _ n.unpair.1.unpair.2) n.unpair.2

def evaln_ropt (s : ℕ) (f : ℕ →. ℕ) [decidable_pred f.dom] : code → ℕ → option ℕ :=
evaln s f.eval_opt

theorem evaln_univn {s f cf} :
  evaln (s+1) f (univn cf) = (λ n, guard (n ≤ s) >> 
  evaln n.unpair.1.unpair.1 (evaln (s+1) f cf) (of_nat _ n.unpair.1.unpair.2) n.unpair.2) :=
funext $ λ n,
by { have : n ≤ s ∨ ¬n ≤ s, exact em (n ≤ s), cases this;
     simp[evaln, (>>), failure, alternative.failure, this],  
     have : min s n.unpair.fst.unpair.fst = n.unpair.1.unpair.1,
     { simp, exact le_trans (nat.unpair_le_left  _) (le_trans (nat.unpair_le_left _) this) },
     rw this }

theorem evaln_univn0 {s f cf} :
  (λ n, guard (n ≤ s) >> 
  evaln (min s n.unpair.1.unpair.1) (evaln (s+1) f cf) (of_nat _ n.unpair.1.unpair.2) n.unpair.2) =
  (λ n, guard (n ≤ s) >> 
  evaln n.unpair.1.unpair.1 (evaln (s+1) f cf) (of_nat _ n.unpair.1.unpair.2) n.unpair.2) :=
funext $ λ n,
by { have : n ≤ s ∨ ¬n ≤ s, exact em (n ≤ s), cases this;
     simp[evaln, (>>), failure, alternative.failure, this], 
     have : min s n.unpair.fst.unpair.fst = n.unpair.1.unpair.1,
     { simp, exact le_trans (nat.unpair_le_left  _) (le_trans (nat.unpair_le_left _) this) },
     rw this }

theorem evaln_inclusion : ∀ {s c} {f g : ℕ → option ℕ},
  (∀ x y, x < s → f x = some y → g x = some y) → 
  ∀ x y, evaln s f c x = some y →  evaln s g c x = some y
| 0 c _ _ := by simp[evaln]
| (s+1) oracle f g := λ h n y, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega,
         cases this; simp[(>>), this], exact h _ _ (nat.lt_succ_iff.mpr this),
         intros _ c, exfalso, exact option.not_mem_none _ c }
| (s+1) zero         f g := by simp[evaln]
| (s+1) succ         f g := by simp[evaln]
| (s+1) left         f g := by simp[evaln]
| (s+1) right        f g := by simp[evaln]
| (s+1) (pair cf cg) f g := λ h n y,
    have IH₀ : _ := @evaln_inclusion (s+1) cf _ _ h,
    have IH₁ : _ := @evaln_inclusion (s+1) cg _ _ h,
    by { simp[evaln, (>>)], assume e hf,
         have : ∃ y, evaln (s + 1) f cf n = some y, 
         { cases evaln (s + 1) f cf n; simp, simp[(<*>), hf] at hf ⊢, exact hf },
         rcases this with ⟨y0, hy0⟩, have IH₀' := IH₀ _ _ hy0,
          have : ∃ y, evaln (s + 1) f cg n = some y, 
         { cases evaln (s + 1) f cg n; simp, simp[(<*>), hf] at hf ⊢, exact hf },
         rcases this with ⟨y1, hy1⟩, have IH₁' := IH₁ _ _ hy1,
         simp[hy0, hy1, IH₀', IH₁'] at hf ⊢, exact ⟨e, hf⟩ }
| (s+1) (comp cf cg) f g := λ h n y,
    have IH₀ : _ := @evaln_inclusion (s+1) cf _ _ h,
    have IH₁ : _ := @evaln_inclusion (s+1) cg _ _ h,
    by { simp[evaln, (>>)], assume e z hz hy,
         refine ⟨e, z, IH₁ _ _ hz, IH₀ _ _ hy⟩ }
| (s+1) (prec cf cg) f g := λ h n y,
    have l0 : ∀ x y, x < s → f x = some y → g x = some y :=
      λ x y e, h x y (nat.lt.step e),
    have IH₀ : _ := @evaln_inclusion s (cf.prec cg) _ _ l0,
    have IH₁ : _ := @evaln_inclusion (s+1) cf _ _ h,
    have IH₂ : _ := @evaln_inclusion (s+1) cg _ _ h,
    by { simp[evaln, (>>)], assume e hf,
         cases n.unpair.snd with n0; simp at hf ⊢, exact ⟨e, IH₁ _ _ hf⟩,
         rcases hf with ⟨z, hz0, hz1⟩,
         refine ⟨e, z, IH₀ _ _ hz0, IH₂ _ _ hz1⟩ }
| (s+1) (rfind' cf)  f g := λ h n y, 
    have l0 : ∀ x y, x < s → f x = some y → g x = some y :=
      λ x y e, h x y (nat.lt.step e),
    have IH₀ : _ := @evaln_inclusion (s+1) cf _ _ h, 
    have IH₁ : _ := @evaln_inclusion s cf.rfind' _ _ l0,
    by { simp[evaln, (>>)], assume e z ez ey,
         refine ⟨e, z, IH₀ _ _ ez, _⟩,
         cases z with z0; simp at ey ⊢, exact ey, exact IH₁ _ _ ey }
| (s+1) (univn cf)  f g := λ h n y, 
    have IH₀ : _ := @evaln_inclusion (s+1) cf _ _ h,
    have IH₀ : _ := @evaln_inclusion
      (min s n.unpair.fst.unpair.fst) (of_nat code n.unpair.fst.unpair.snd)
      (evaln (s + 1) f cf) (evaln (s + 1) g cf) (λ x y _, IH₀ x y),
    by { simp[evaln, (>>)], assume e ey, refine ⟨e, IH₀ _ _ ey⟩ }

theorem evaln_use : ∀ {s c} {f g : ℕ → option ℕ},
  (∀ x, x < s → f x = g x) → evaln s f c = evaln s g c
| 0     c            _ _  := by simp[evaln]
| (s+1) oracle       _ _  := λ h, funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega,
         cases this; simp[(>>), this], exact h _ (nat.lt_succ_iff.mpr this), refl }
| (s+1) zero         f g := by simp[evaln]
| (s+1) succ         f g := by simp[evaln]
| (s+1) left         f g := by simp[evaln]
| (s+1) right        f g := by simp[evaln]
| (s+1) (pair cf cg) f g := λ h,
    have IH₀ : _ := @evaln_use (s+1) cf _ _ h,
    have IH₁ : _ := @evaln_use (s+1) cg _ _ h,
    funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀, IH₁] }
| (s+1) (comp cf cg) f g := λ h,
    have IH₀ : _ := @evaln_use (s+1) cf _ _ h,
    have IH₁ : _ := @evaln_use (s+1) cg _ _ h,
    funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀, IH₁] }
| (s+1) (prec cf cg) f g := λ h,
    have l0 : ∀ (x : ℕ), x < s → f x = g x := λ x e, h x (nat.lt.step e),
    have IH₀ : _ := @evaln_use s (cf.prec cg) _ _ l0,
    have IH₁ : _ := @evaln_use (s+1) cf _ _ h,
    have IH₂ : _ := @evaln_use (s+1) cg _ _ h,
    funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀, IH₁, IH₂] }
| (s+1) (rfind' cf)  f g := λ h, 
    have l0 : ∀ (x : ℕ), x < s → f x = g x := λ x e, h x (nat.lt.step e),
    have IH₀ : _ := @evaln_use (s+1) cf _ _ h,
    have IH₁ : _ := @evaln_use s cf.rfind' _ _ l0,
    funext $ λ n, 
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀, IH₁] }
| (s+1) (univn cf)   f g := λ h, funext $ λ n,
    have IH₀ : _ := @evaln_use (s+1) cf _ _ h,
    have IH₀ : _ := @evaln_use
      (min s n.unpair.fst.unpair.fst) (of_nat code n.unpair.fst.unpair.snd)
      (evaln (s + 1) f cf) (evaln (s + 1) g cf) (by simp[IH₀]),
    by { simp[evaln], have : n ≤ s ∨ ¬ n ≤ s, omega, cases this;
         simp[(>>), this, IH₀] }

theorem evaln_use' {s} {f g : ℕ → option ℕ} (h : ∀ x, x < s → f x = g x) :
  evaln s f = evaln s g := 
funext $ λ c, evaln_use h

def evaln_univn_oracle (f) (c : code) {s s' a : ℕ} (h : (s'.mkpair (encode c)).mkpair a < s) :
  evaln s f (univn oracle) ((s'.mkpair (encode c)).mkpair a) = evaln s' f c a :=
begin
  suffices : evaln s f (univn oracle) ((s'.mkpair (encode c)).mkpair a) =
  evaln s' (λ n, guard (n < s) >> f n) c a,
  { rw this, 
    have : ∀ x, x < s' → (λ n, guard (n < s) >> f n) x = f x,
    { intros x ex, 
      have : x < s := 
      lt_trans (lt_of_lt_of_le ex (le_trans (nat.le_mkpair_left _ _) (nat.le_mkpair_left _ _))) h,
      simp[(>>), this] },
    have := evaln_use' this, simp[this] },
  have e0 : s = (s - 1) + 1, omega, rw e0,
  have e : min (s - 1) s' = s', simp,
  { suffices : s' < s, omega,
    exact lt_of_le_of_lt (le_trans (nat.le_mkpair_left _ _) (nat.le_mkpair_left _ _)) h },
  have : (s'.mkpair (encode c)).mkpair a ≤ s - 1, omega,
  simp[evaln, this, e, pure],
  suffices : (λ (n : ℕ), guard (n ≤ s - 1) >> f n) =
    (λ (n : ℕ), guard (n < s - 1 + 1) >> f n),
  rw this, simp[this, (>>)], funext x, 
  have : x ≤ s - 1 ↔ x < s - 1 + 1, from nat.lt_succ_iff.symm,
  simp[this], congr,
end

theorem evaln_bound {f} : ∀ {k c n x}, x ∈ evaln k f c n → n < k
| 0     c n x h := by simp [evaln] at h; cases h
| (k+1) c n x h := begin
  suffices : ∀ {o : option ℕ}, x ∈ guard (n ≤ k) >> o → n < k + 1,
  { cases c; rw [evaln] at h; try { exact this h } },
  simpa [(>>)] using nat.lt_succ_of_le
end

theorem evaln_mono : ∀ {s₁ s₂ c f n x},
  s₁ ≤ s₂ → evaln s₁ f c n = some x → evaln s₂ f c n = some x
| 0      _      _            _ _ _ := λ _ h, by simp [evaln] at h; cases h
| (s₀+1) 0      _            _ _ _ := λ e h, by exfalso; exact nat.not_succ_le_zero s₀ e
| (s₀+1) (s₁+1) oracle       f n x := λ hs,
    by { simp[evaln], have : n ≤ s₀ ∨ ¬ n ≤ s₀, omega,
         cases this; simp[(>>), this], exact λ e, ⟨by omega, e⟩,
         intros _ c, exfalso, exact option.not_mem_none _ c }
| (s₀+1) (s₁+1) zero         f n x := λ hs, 
    by simp[evaln, (>>)]; exact λ _ e, ⟨by omega, e⟩
| (s₀+1) (s₁+1) succ         f n x := λ hs, 
    by simp[evaln, (>>)]; exact λ _ e, ⟨by omega, e⟩
| (s₀+1) (s₁+1) left         f n x := λ hs, 
    by simp[evaln, (>>)]; exact λ _ e, ⟨by omega, e⟩
| (s₀+1) (s₁+1) right        f n x := λ hs, 
    by simp[evaln, (>>)]; exact λ _ e, ⟨by omega, e⟩
| (s₀+1) (s₁+1) (pair cf cg) f n x := λ hs,
    have IH₀ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f n y hs,
    have IH₁ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cg f n y hs,
    by { simp[evaln, (>>)], assume e0 ex,
         have : ∃ y, evaln (s₀ + 1) f cf n = some y,
         { cases evaln (s₀ + 1) f cf n; simp[(<*>)] at ex ⊢, exact ex },
         rcases this with ⟨y₀, hy₀⟩,
         have : ∃ y, evaln (s₀ + 1) f cg n = some y,
         { cases evaln (s₀ + 1) f cg n; simp[(<*>)] at ex ⊢, exact ex },         
         rcases this with ⟨y₁, hy₁⟩,
         simp[hy₀, hy₁, IH₀ _ _ hy₀, IH₁ _ _ hy₁] at ex ⊢,
         exact ⟨le_trans e0 (nat.le_of_succ_le_succ hs), ex⟩ }
| (s₀+1) (s₁+1) (comp cf cg) f n x := λ hs,        
    have IH₀ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f n y hs,
    have IH₁ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cg f n y hs,
    by { simp[evaln, (>>)], assume e0 y ey ex,
         refine ⟨le_trans e0 (nat.le_of_succ_le_succ hs), y, IH₁ _ _ ey, IH₀ _ _ ex⟩ }
| (s₀+1) (s₁+1) (prec cf cg) f n x := λ hs,
    have IH₀ : _ := λ n y, @evaln_mono s₀ s₁ (cf.prec cg) f n y (nat.le_of_succ_le_succ hs),
    have IH₁ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f n y hs,
    have IH₂ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cg f n y hs,
    by { simp[evaln, (>>)],
         cases n.unpair.snd with n0; simp,
         assume e0 ex,
         exact ⟨le_trans e0 (nat.le_of_succ_le_succ hs), IH₁ _ _ ex⟩,
         assume e0 y ey ex,
         refine ⟨le_trans e0 (nat.le_of_succ_le_succ hs), y, IH₀ _ _ ey, IH₂ _ _ ex⟩ }
| (s₀+1) (s₁+1) (rfind' cf)  f n x := λ hs,
    have IH₀ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f n y hs,
    have IH₁ : _ := λ n y, @evaln_mono s₀ s₁ cf.rfind' f n y (nat.le_of_succ_le_succ hs),
    by { simp[evaln, (>>), pure],
         assume e0 y ey ex,
         refine ⟨by omega, y, IH₀ _ _ ey, _⟩,
         cases y with y0; simp at ex ⊢, exact ex, exact IH₁ _ _ ex }
| (s₀+1) (s₁+1) (univn cf)   f n x := λ hs,
    have IH₀ : _ := λ n y, @evaln_mono (s₀+1) (s₁+1) cf f n y hs,
    have IH₁ : _ := λ n y : ℕ, @evaln_mono
      (min s₀ n.unpair.1.unpair.1) (min s₁ n.unpair.1.unpair.1)
      (of_nat code n.unpair.fst.unpair.snd)
      (evaln (s₀ + 1) f cf) n.unpair.2 y,
    by { simp[evaln, (>>)], assume e ex,
         have : min s₀ n.unpair.fst.unpair.fst ≤ min s₁ n.unpair.fst.unpair.fst :=
         inf_le_inf_right _ (nat.le_of_succ_le_succ hs),
         have := IH₁ _ _ this ex, refine ⟨by omega, _⟩,
         exact evaln_inclusion (λ x y _, IH₀ x y) _ _ this }

def eval (f : ℕ → option ℕ) : code → ℕ →. ℕ 
| oracle := λ n, f n
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
| (univn cf) := λ n, nat.rfind_opt
    (λ s, guard (n ≤ s) >> evaln n.unpair.1.unpair.1 
      (evaln (s+1) f cf) (of_nat _ n.unpair.1.unpair.2) n.unpair.2)

lemma eval_univn_evaln_iff {f x n} {cf : code} :
  x ∈ eval f cf.univn n ↔ (∃ k, evaln (k + 1) f cf.univn n = some x) :=
begin
  simp[eval, evaln_univn, (>>)],
  let f := (λ s, guard (n ≤ s) >> evaln n.unpair.1.unpair.1
    (evaln (s+1) f cf) (of_nat _ n.unpair.1.unpair.2) n.unpair.2),
  have : ∀ a m n, m ≤ n → a ∈ f m → a ∈ f n,
  { simp[f, (>>)], intros a s₀ s₁ e e0 ha, refine ⟨by omega, evaln_inclusion _ _ _ ha⟩, 
    exact (λ x y _, evaln_mono (by omega)) },
  have := (@nat.rfind_opt_mono _ _ this) x, simp [f, (>>)] at this, 
  exact this
end

theorem evaln_sound {f} : ∀ {s c n x},
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
| (s + 1) (univn cf) n x h := eval_univn_evaln_iff.mpr ⟨s, h⟩

theorem evaln_complete {f : ℕ → option ℕ} {c n x} :
  x ∈ eval (λ x, f x) c n ↔ ∃ k, x ∈ evaln k f c n := ⟨λ h,
begin
  suffices : ∃ k, x ∈ evaln (k+1) f c n,
  { exact let ⟨k, h⟩ := this in ⟨k+1, h⟩ },
    induction c generalizing n x;
    simp [eval, evaln, pure, pfun.pure, (<*>), (>>)] at h ⊢,
    { exact ⟨⟨n, by refl⟩, h⟩ },
    { use n, have : min n n.unpair.fst.unpair.fst = n.unpair.fst.unpair.fst,
      { simp, exact le_trans (nat.unpair_le_left _) (nat.unpair_le_left _) }, simp [this,h] },
    { exact ⟨⟨_, le_refl _⟩, h.symm⟩ },
    { exact ⟨⟨_, le_refl _⟩, h.symm⟩ },
    { exact ⟨⟨_, le_refl _⟩, h.symm⟩ },
    case nat.rpartrec.code.pair : cf cg hf hg 
    { rcases h with ⟨x, hx, y, hy, rfl⟩,
      rcases hf hx with ⟨k₁, hk₁⟩, rcases hg hy with ⟨k₂, hk₂⟩,
      refine ⟨max k₁ k₂, le_max_left_of_le $ nat.le_of_lt_succ $ evaln_bound hk₁, x, _, y, _, rfl⟩,
      exact evaln_mono (nat.succ_le_succ $ le_max_left _ _) hk₁, 
      exact evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk₂ },
    case nat.rpartrec.code.comp : cf cg hf hg 
    { rcases h with ⟨y, hy, hx⟩,
      rcases hf hx with ⟨k₁, hk₁⟩, rcases hg hy with ⟨k₂, hk₂⟩,
      refine ⟨max k₂ k₁, le_max_left_of_le $ nat.le_of_lt_succ $ evaln_bound hk₂, y, _, _⟩,
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
        refine ⟨(max k₁ k₂).succ, nat.le_succ_of_le $ le_max_left_of_le $
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
        use (nat.le_succ_of_le $ le_max_left_of_le $ nat.le_of_lt_succ $ evaln_bound hk₁),
        use a,
        use evaln_mono (nat.succ_le_succ $ nat.le_succ_of_le $ le_max_left _ _) hk₁,
        simpa [nat.succ_eq_add_one, a0, -max_eq_left, -max_eq_right, add_comm, add_left_comm] using
            evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk₂ } },
    case nat.rpartrec.code.univn : cf hf
    { have := eval_univn_evaln_iff.mp h, simp[evaln, (>>)] at this, exact this }
end, λ ⟨k, h⟩, evaln_sound h⟩

@[simp] theorem eval_const (f) : ∀ n m, eval f (code.const n) m = roption.some n
| 0     m := rfl
| (n+1) m := by simp! *

@[simp] theorem eval_id (f n) : eval f code.id n = roption.some n := by simp! [(<*>)]

@[simp] theorem eval_curry (f c n x) : eval f (curry c n) x = eval f c (mkpair n x) :=
by simp! [(<*>)]

end nat.rpartrec.code