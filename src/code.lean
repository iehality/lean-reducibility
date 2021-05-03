import computability.partrec
import computability.partrec_code
import data.pfun
import tactic
import rpartrec

open encodable denumerable roption

@[simp] lemma eval_eval_opt {α β} (f : α →. β) [D : decidable_pred f.dom] {x} :
  f.eval_opt x = @roption.to_option _ (f x) (D x) := rfl

@[simp] theorem mem_to_option' {α} {o : roption α} [decidable o.dom] {a : α} :
  to_option o = some a ↔ a ∈ o := mem_to_option

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

lemma guygk (n) : n ≤ n+9 := nat.le.intro rfl

def of_nat_code : ℕ → code
| 0 := oracle
| 1 := zero
| 2 := succ
| 3 := left
| 4 := right
| (e+5) :=
  have div8 : e.div2.div2 ≤ e :=
    by { simp[nat.div2_val], 
         exact le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2) },
  have e.div2.div2 < e + 5 := nat.lt_succ_iff.mpr (le_trans div8 (nat.le.intro rfl)),
  have e.div2.div2.unpair.1 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_le_left _) div8) (nat.le.intro rfl)),
  have e.div2.div2.unpair.2 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_le_right _) div8) (nat.le.intro rfl)),
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
| 0     := rfl
| 1     := rfl
| 2     := rfl
| 3     := rfl
| 4     := rfl
| (e+5) :=
have div8 : e.div2.div2 ≤ e :=
    by { simp[nat.div2_val], 
         exact le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2) },
  have e.div2.div2 < e + 5 := nat.lt_succ_iff.mpr (le_trans div8 (nat.le.intro rfl)),
  have e.div2.div2.unpair.1 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_le_left _) div8) (nat.le.intro rfl)),
  have e.div2.div2.unpair.2 < e + 5 := nat.lt_succ_iff.mpr
    (le_trans (le_trans (nat.unpair_le_right _) div8) (nat.le.intro rfl)),
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

def evaln_ropt (s : ℕ) (f : ℕ →. ℕ) [decidable_pred f.dom] : code → ℕ → option ℕ :=
evaln s f.eval_opt

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

theorem evaln_use' {s} {f g : ℕ → option ℕ} (h : ∀ x, x < s → f x = g x) :
  evaln s f = evaln s g := 
funext $ λ c, evaln_use h

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

def eval_ropt (f : ℕ →. ℕ) [decidable_pred f.dom] : code → ℕ →. ℕ :=
eval f.eval_opt

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
end, λ ⟨k, h⟩, evaln_sound h⟩

theorem evaln_complete_dec {c f} [D : decidable_pred (eval f c).dom] : ∀ m, ∃ s₀,
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

@[simp] theorem eval_const (f) : ∀ n m, eval f (code.const n) m = roption.some n
| 0     m := rfl
| (n+1) m := by simp! *

@[simp] theorem eval_id (f n) : eval f code.id n = roption.some n := by simp! [(<*>)]

@[simp] theorem eval_curry (f c n x) : eval f (curry c n) x = eval f c (mkpair n x) :=
by simp! [(<*>)]


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
  have := (rpartrec.rfind.trans (c₂.map c₁.to_comp.to_rcomp)).map c₀.to_comp.to_rcomp,
  simp at this,
  exact this.comp primrec.unpair.to_comp.to_rcomp
end

theorem exists_code {f g : ℕ →. ℕ} [D : decidable_pred g.dom] :
  nat.rpartrec g f ↔ ∃ c, eval (g.eval_opt) c = f := ⟨λ h,
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
end,λ h, begin
  rcases h with ⟨c, rfl⟩, induction c,
  case nat.rpartrec.code.oracle 
  { simp[eval], unfold_coes, simp, exact nat.rpartrec.oracle },
  case nat.rpartrec.code.zero { exact nat.rpartrec.zero },
  case nat.rpartrec.code.succ { exact nat.rpartrec.succ },
  case nat.rpartrec.code.left { exact nat.rpartrec.left },
  case nat.rpartrec.code.right { exact nat.rpartrec.right },
  case nat.rpartrec.code.pair : cf cg pf pg { exact pf.pair pg },
  case nat.rpartrec.code.comp : cf cg pf pg { exact pf.comp pg },
  case nat.rpartrec.code.prec : cf cg pf pg { exact pf.prec pg },
  case nat.rpartrec.code.rfind' : cf pf { exact nat.rpartrec.trans rpartrec_rfind' pf },
end⟩

theorem exists_code_opt {f : ℕ →. ℕ} {g : ℕ → option ℕ} :
  nat.rpartrec (λ x, g x) f ↔ ∃ c, eval g c = f := ⟨λ h,
begin
  induction h,
  case nat.rpartrec.oracle 
  { exact ⟨oracle, rfl⟩ },  
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

#check exists_code
open rcomputable

axiom evaln_computable (f : ℕ →. ℕ) [decidable_pred f.dom] : 
  (λ x : (ℕ × code) × ℕ, evaln_ropt x.1.1 f x.1.2 x.2) computable_in f 

axiom evaln_ropt_computable (f : ℕ →. ℕ) [decidable_pred f.dom] : 
  (λ x : (ℕ × code) × ℕ, evaln_ropt x.1.1 f x.1.2 x.2) computable_in f 

theorem eval_eq_rfind_opt (f : ℕ →. ℕ) [decidable_pred f.dom] (c n) :
  eval_ropt f c n = nat.rfind_opt (λ k, evaln_ropt k f c n) :=
roption.ext $ λ x, begin
  refine evaln_complete.trans (nat.rfind_opt_mono _).symm,
  intros a m n hl, apply evaln_mono hl,
end

theorem eval_partrec (f : ℕ →. ℕ) [decidable_pred f.dom] :
  (λ n : code × ℕ, eval_ropt f n.1 n.2) partrec_in f :=
begin
  have := ((evaln_computable f).comp ((snd.pair $ fst.comp fst).pair $ snd.comp fst)),
  have := rpartrec.rfind_opt this,
  exact (this.of_eq $ λ n, by simp[eval_eq_rfind_opt])
end 

end nat.rpartrec.code

namespace rpartrec
open rcomputable nat.rpartrec 

variables {α : Type*} {σ : Type*} {β : Type*} {τ : Type*} 
variables [primcodable α] [primcodable σ] [primcodable β] [primcodable τ]

instance (f : β →. τ) [D : decidable_pred f.dom] :
  decidable_pred (pfun.dom (λ n, (roption.bind (decode β n) (λ a, (f a).map encode)))) := λ a,
by{ simp[decidable_pred,pfun.dom,set.set_of_app_iff], cases decode β a with b; simp[roption.none, roption.some],
    exact decidable.false, exact D b }

def univn (s : ℕ) (f : β →. τ) [decidable_pred f.dom] (e : ℕ) : α →. σ := (λ a,
(code.evaln_ropt s 
  (λ n, (roption.bind (decode β n) (λ a, (f a).map encode)))
  (of_nat code e) (encode a))
.bind (λ x, (decode σ x)))

notation `⟦`e`⟧^`f:max` [`s`]` := univn s f e

def univ (f : β →. τ) [decidable_pred f.dom] (e : ℕ) : α →. σ := (λ a,
(code.eval_ropt 
  (λ n, (roption.bind (decode β n) (λ a, (f a).map encode)))
  (of_nat code e) (encode a))
.bind (λ x, (decode σ x)))

notation `⟦`e`⟧^`f:max := univ f e

theorem evaln_sound {e} {f : β →. τ} [decidable_pred f.dom] {x : α} {y : σ} {s : ℕ} :
  ⟦e⟧^f [s] x = some y → ⟦e⟧^f x = some y := 
by{ simp[univn, univ, roption.eq_some_iff], 
    exact λ s h e, ⟨s, code.evaln_sound h, e⟩ }

#check code.eval_partrec

theorem rpartrec_univ_iff {f : α →. σ} {g : β →. τ} [decidable_pred g.dom] :
  f partrec_in (g : β →. τ) ↔ ∃ e, ⟦e⟧^g = f :=
begin
  simp[univn, univ, rpartrec, nat.rpartrec.reducible, roption.eq_some_iff],
      let g' := (λ (n : ℕ), option.bind (decode β n) (λ (a : β), some (encode (g a)))),
    have : (λ (n : ℕ), roption.bind (decode β n) (λ (a : β), some (encode (g a)))) =
      (λ x, g' x : ℕ →. ℕ) := funext (λ x, 
      by { unfold_coes, simp[g'], cases decode β x; simp[roption.of_option, (>>=)] }),
    rw [this],
  split,
  { simp only [nat.rpartrec.code.exists_code_opt], 
    rintros ⟨c, hc⟩, refine ⟨encode c, funext $ λ a, _⟩, simp, unfold_coes, simp[roption.of_option,hc] },
  { rintros ⟨e, he⟩, simp[←he], unfold_coes, 
    have : (λ a : α,
      (code.eval g' (of_nat code e) (encode a)).bind
      (λ y, roption.map encode (roption.of_option (decode σ y)))) partrec_in (λ (x : ℕ), roption.of_option (g' x)),
        }
  --{ assume h,
  --  rcases nat.rpartrec.code.exists_code_opt.mp h with ⟨c, hc⟩, 
  --  refine ⟨encode c, funext $ λ a, _⟩, simp, simp[g'] at hc, unfold_coes, simp[roption.of_option,hc] },
  --{ rintros ⟨e, he⟩,
  --  
  --  }
  
end


end rpartrec