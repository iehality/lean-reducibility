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

theorem mem_to_option_none {α} {o : roption α} [D : decidable o.dom] {a : α} :
  to_option o = none ↔ o = none :=
by { unfold to_option, by_cases h : o.dom; simp [h],
     { exact λ h0, roption.eq_none_iff'.mp h0 h },
     { exact roption.eq_none_iff'.mpr h } }

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

def oracle_of (c : code) : code → code
| oracle       := c
| zero         := zero
| succ         := succ
| left         := left
| right        := right
| (pair cf cg) := pair (oracle_of cf) (oracle_of cg)
| (comp cf cg) := comp (oracle_of cf) (oracle_of cg)
| (prec cf cg) := prec (oracle_of cf) (oracle_of cg)
| (rfind' cf)  := rfind' (oracle_of cf)

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

theorem evaln_inclusion : ∀ {s c} {f g : ℕ → option ℕ},
  (∀ x y, x < s → f x = some y → g x = some y) → 
  ∀ {x y}, evaln s f c x = some y →  evaln s g c x = some y
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
         rcases this with ⟨y0, hy0⟩, have IH₀' := IH₀ hy0,
          have : ∃ y, evaln (s + 1) f cg n = some y, 
         { cases evaln (s + 1) f cg n; simp, simp[(<*>), hf] at hf ⊢, exact hf },
         rcases this with ⟨y1, hy1⟩, have IH₁' := IH₁ hy1,
         simp[hy0, hy1, IH₀', IH₁'] at hf ⊢, exact ⟨e, hf⟩ }
| (s+1) (comp cf cg) f g := λ h n y,
    have IH₀ : _ := @evaln_inclusion (s+1) cf _ _ h,
    have IH₁ : _ := @evaln_inclusion (s+1) cg _ _ h,
    by { simp[evaln, (>>)], assume e z hz hy,
         refine ⟨e, z, IH₁ hz, IH₀ hy⟩ }
| (s+1) (prec cf cg) f g := λ h n y,
    have l0 : ∀ x y, x < s → f x = some y → g x = some y :=
      λ x y e, h x y (nat.lt.step e),
    have IH₀ : _ := @evaln_inclusion s (cf.prec cg) _ _ l0,
    have IH₁ : _ := @evaln_inclusion (s+1) cf _ _ h,
    have IH₂ : _ := @evaln_inclusion (s+1) cg _ _ h,
    by { simp[evaln, (>>)], assume e hf,
         cases n.unpair.snd with n0; simp at hf ⊢, exact ⟨e, IH₁ hf⟩,
         rcases hf with ⟨z, hz0, hz1⟩,
         refine ⟨e, z, IH₀ hz0, IH₂ hz1⟩ }
| (s+1) (rfind' cf)  f g := λ h n y, 
    have l0 : ∀ x y, x < s → f x = some y → g x = some y :=
      λ x y e, h x y (nat.lt.step e),
    have IH₀ : _ := @evaln_inclusion (s+1) cf _ _ h, 
    have IH₁ : _ := @evaln_inclusion s cf.rfind' _ _ l0,
    by { simp[evaln, (>>)], assume e z ez ey,
         refine ⟨e, z, IH₀ ez, _⟩,
         cases z with z0; simp at ey ⊢, exact ey, exact IH₁ ey }

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

theorem eval_inclusion {c x y} {f : ℕ → option ℕ} (h : y ∈ eval f c x) : ∃ s, ∀ {g : ℕ → option ℕ},
  (∀ x y, x < s → f x = some y → g x = some y) → y ∈ eval g c x :=
by { have : ∃ s, y ∈ evaln s f c x := evaln_complete.mp h, rcases this with ⟨s, hs⟩,
     refine ⟨s, λ g h, evaln_complete.mpr ⟨s, evaln_inclusion h hs⟩⟩ }

@[simp] theorem eval_const (f) : ∀ n m, eval f (code.const n) m = roption.some n
| 0     m := rfl
| (n+1) m := by simp! *

@[simp] theorem eval_id (f n) : eval f code.id n = roption.some n := by simp! [(<*>)]

@[simp] theorem eval_curry (f c n x) : eval f (curry c n) x = eval f c (mkpair n x) :=
by simp! [(<*>)]

@[simp] theorem oracle_of_eq {g h : ℕ → option ℕ} {cg : code} (hg : eval h cg = λ x, g x) :
  ∀ cf, eval h (oracle_of cg cf) = eval g cf
| oracle := by simp[eval, oracle_of, hg]
| zero   := by simp[eval, oracle_of]
| succ   := by simp[eval, oracle_of]
| left   := by simp[eval, oracle_of]
| right   := by simp[eval, oracle_of]
| (pair cff cfg) := by {
    have IH₀ := oracle_of_eq cff,
    have IH₁ := oracle_of_eq cfg,
    simp[eval, oracle_of, IH₀, IH₁] }
| (comp cff cfg) := by {
    have IH₀ := oracle_of_eq cff,
    have IH₁ := oracle_of_eq cfg,
    simp[eval, oracle_of, IH₀, IH₁] }
| (prec cff cfg) := by {
    have IH₀ := oracle_of_eq cff,
    have IH₁ := oracle_of_eq cfg,
    simp[eval, oracle_of, IH₀, IH₁] }
| (rfind' cff) := by {
    have IH₀ := oracle_of_eq cff,
    simp[eval, oracle_of, IH₀] }

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

theorem oracle_of_prim : primrec₂ oracle_of :=
by sorry

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

open rcomputable

axiom evaln_computable (f : ℕ → option ℕ) : 
  (λ x : (ℕ × code) × ℕ, evaln x.1.1 f x.1.2 x.2) computable_in (λ x, f x) 

theorem eval_eq_rfind (f : ℕ → option ℕ) (c n) :
  eval f c n = nat.rfind_opt (λ k, evaln k f c n) :=
roption.ext $ λ x, begin
  refine evaln_complete.trans (nat.rfind_opt_mono _).symm,
  intros a m n hl, apply evaln_mono hl,
end

theorem eval_partrec (f : ℕ → option ℕ) :
  (λ n : code × ℕ, eval f n.1 n.2) partrec_in (λ x, f x) :=
begin
  have := ((evaln_computable f).comp ((snd.pair $ fst.comp fst).pair $ snd.comp fst)),
  have := rpartrec.rfind_opt this,
  exact (this.of_eq $ λ n, by simp[eval_eq_rfind])
end 

end nat.rpartrec.code
open nat.rpartrec 

variables {α : Type*} {σ : Type*} {β : Type*} {τ : Type*} {γ : Type*} {μ : Type*} 
variables [primcodable α] [primcodable σ] [primcodable β] [primcodable τ] [primcodable γ] [primcodable μ]

def univn (α σ) [primcodable α] [primcodable σ] (s : ℕ) (f : β → option τ) (e : ℕ) : α → option σ := (λ a,
(code.evaln s 
  (λ n, (decode β n).bind (λ a, (f a).map encode ))
  (of_nat code e) (encode a))
.bind (λ x, (decode σ x)))

notation `⟦`e`⟧^`f:max` [`s`]` := univn _ _ s f e

def univ (α σ) [primcodable α] [primcodable σ] (f : β → option τ) (e : ℕ) : α →. σ := (λ a,
(code.eval
  (λ n, (decode β n).bind (λ a, (f a).map encode))
  (of_nat code e) (encode a))
.bind (λ x, (decode σ x)))

notation `⟦`e`⟧^`f:max := univ _ _ f e

def curry {α} [primcodable α] (e : ℕ) (n : α) : ℕ := encode (code.curry (of_nat _ e) (encode n))

def oracle_of (e i : ℕ) : ℕ := encode (code.oracle_of (of_nat _ e) (of_nat _ i))

@[simp] theorem eval_curry (f : γ → option τ) (e n x) :
  univ α σ f (curry e n) x = univ (β × α) σ f e (n, x) :=
by { simp[curry, univ] }

namespace rpartrec

theorem curry_prim {α} [primcodable α] : primrec₂ (@curry α _) :=
(primrec.encode.comp $ code.curry_prim.comp 
  ((primrec.of_nat code).comp primrec.fst) ((@primrec.encode α _).comp primrec.snd))

open primrec
theorem univn_rcomputable (α σ) [primcodable α] [primcodable σ] (f : β → option τ) :
  (λ x, ⟦x.2.1⟧^f [x.1] x.2.2 : ℕ × ℕ × α → option σ) computable_in (λ x, f x) :=
begin
  simp[univn], unfold_coes,
  let f1 := (λ (n : ℕ), (decode β n).bind (λ (a : β), option.map encode (f a))),
    have c₁ : (λ n, roption.of_option (f1 n)) partrec_in (λ x, roption.of_option (f x)),
  { simp[f1],
    have e : (λ (n : ℕ), roption.of_option ((decode β n).bind (λ (a : β), (f a).map encode ))) =
      (λ (n : ℕ), roption.bind (decode β n) (λ (a : β), roption.map encode (f a))),
    { funext a, cases decode β a with v; simp[roption.of_option],
      cases f v; simp[(>>=), roption.of_option], },
    rw e,
    have := (refl_in (λ (x : β), roption.of_option (f x))).map (primrec.encode.comp snd).to_comp.to_rcomp, 
    have := (computable.of_option (computable.decode)).to_rpart.bind (this.comp rcomputable.snd),
    simp at this,
    exact this },
  have c₀ := (code.evaln_computable f1).comp 
    ((fst.pair ((primrec.of_nat code).comp $ fst.comp snd)).pair
    (primrec.encode.comp $ snd.comp snd)).to_comp.to_rcomp,
  have := rpartrec.trans c₀ c₁,
  have c₂ : (λ (a : ℕ × ℕ × α), code.evaln a.fst f1 (of_nat code a.snd.fst) (encode a.snd.snd))
    computable_in (λ (x : β), roption.of_option (f x)) := this,
  have c₃ := primrec.decode.comp snd,
  have := c₂.option_bind c₃.to_comp.to_rcomp,
  exact this,
end

--open rcomputable
theorem univ_rpartrec (α σ) [primcodable α] [primcodable σ] (f : β → option τ) :
  (λ x, ⟦x.1⟧^f x.2 : ℕ × α →. σ) partrec_in (λ x, f x) :=
begin
  simp[univ], unfold_coes,
  let f1 := (λ (n : ℕ), (decode β n).bind (λ (a : β), option.map encode (f a))),
  have c₁ : (λ n, roption.of_option (f1 n)) partrec_in (λ x, roption.of_option (f x)),
  { simp[f1],
    have e : (λ (n : ℕ), roption.of_option ((decode β n).bind (λ (a : β), (f a).map encode ))) =
      (λ (n : ℕ), roption.bind (decode β n) (λ (a : β), roption.map encode (f a))),
    { funext a, cases decode β a with v; simp[roption.of_option],
      cases f v; simp[(>>=), roption.of_option], },
    rw e,
    have := (refl_in (λ (x : β), roption.of_option (f x))).map (primrec.encode.comp snd).to_comp.to_rcomp, 
    have := ((computable.decode).of_option).to_rpart.bind (this.comp rcomputable.snd), simp at this,
    exact this },
  have c₀ := (code.eval_partrec f1).comp 
    (((primrec.of_nat code).comp fst).pair
    (primrec.encode.comp snd)).to_comp.to_rcomp,
  have c₂ := c₀.trans c₁,
  have c₃ := computable.decode.of_option ,
  have := c₂.bind (c₃.to_rpart.comp rcomputable.snd),
  exact this,
end

theorem evaln_sound {e} {f : β → option τ} {x : α} {y : σ} {s : ℕ} :
  ⟦e⟧^f [s] x = some y → ⟦e⟧^f x = some y := 
by{ simp[univn, univ, roption.eq_some_iff], 
    exact λ s h e, ⟨s, code.evaln_sound h, e⟩ }

theorem evaln_complete {f : β → option τ} {e x} {n : α} :
  x ∈ (⟦e⟧^f n : roption σ) ↔ ∃ s, ⟦e⟧^f [s] n = some x :=
by{ simp[univn, univ, roption.eq_some_iff], split,
    { rintros ⟨a, ha, ea⟩,
      rcases code.evaln_complete.mp ha with ⟨s, hs⟩,
      refine ⟨s, a, hs, ea⟩ },
    { rintros ⟨s, a, ha, ea⟩,
      have := code.evaln_complete.mpr ⟨s, ha⟩,
      refine ⟨a, this, ea⟩ } }

theorem rpartrec_univ_iff {f : α →. σ} {g : β → option τ} :
  f partrec_in (λ x, g x) ↔ ∃ e, ⟦e⟧^g = f :=
begin
  simp[univn, univ, rpartrec, nat.rpartrec.reducible, roption.eq_some_iff], unfold_coes,
  let g' := (λ n, (decode β n).bind (λ a, (g a).map encode)),
  have : (λ n, (roption.of_option (decode β n)).bind (λ a, roption.map encode (roption.of_option (g a)))) =
    (λ x, g' x : ℕ →. ℕ) := funext (λ x, 
  by { unfold_coes, simp[g'], cases decode β x with v; simp[roption.of_option, (>>=)],
       cases g v; simp[roption.of_option, (>>=)] }),
  simp [this], split,
  { assume h, rcases nat.rpartrec.code.exists_code_opt.mp h with ⟨c, hc⟩, 
    refine ⟨encode c, funext $ λ a, _⟩, simp, simp[roption.of_option,hc] },
  { rintros ⟨e, he⟩, simp[←he, g'], 
    have c₀ := (code.eval_partrec g').comp 
      ((computable.const (of_nat code e)).to_rcomp.pair computable.encode.to_rcomp),
    have c₁ := (computable.of_option computable.decode).map (computable.encode.comp computable.snd).to₂,
    have c₂ := c₀.bind (c₁.comp computable.snd).to_rpart,
    have := computable.of_option computable.decode,
    have := this.to_rpart.bind (c₂.comp rcomputable.snd), 
    exact rpartrec.nat_iff.mp this }
end

theorem rpartrec_univ_iff_total {f : α →. σ} {g : β → τ} :
  f partrec_in pfun.lift g ↔ ∃ e, ⟦e⟧^(λ x, some $ g x) = f :=
by { rw ← rpartrec_univ_iff, simp[roption.of_option], refl }

theorem eval_inclusion {e} {x : α} {y : σ}
  {f : ℕ → option τ} (h : y ∈ (⟦e⟧^f x : roption σ)) : ∃ s, ∀ {g : ℕ → option τ},
  (∀ x y, x < s → f x = some y → g x = some y) → y ∈ (⟦e⟧^g x : roption σ) := 
by { simp [roption.eq_some_iff, univ] at h ⊢, rcases h with ⟨a, h, e⟩,
     rcases nat.rpartrec.code.eval_inclusion h with ⟨s, hs⟩,
     refine ⟨s, λ g h, ⟨a, hs (λ x y e ey, _), e⟩⟩, simp at ey, rcases ey with ⟨a, ea, ey⟩,
     have := h _ _ e ea, simp[this, ey] }

protected theorem cond {c : α → bool} {f : α →. σ} {g : α →. σ} {h : β → τ}
  (hc : c computable_in (h : β →. τ)) (hf : f partrec_in (h : β →. τ)) (hg : g partrec_in (h : β →. τ)) :
  (λ a, cond (c a) (f a) (g a)) partrec_in (h : β →. τ) :=
let h' : β → option τ := (λ x, some (h x)) in
have lf : f partrec_in (λ x, h' x), { simp[h'], exact hf },
have lg : g partrec_in (λ x, h' x), { simp[h'], exact hg },
let ⟨e, hf⟩ := rpartrec_univ_iff.1 lf,
    ⟨i, hg⟩ := rpartrec_univ_iff.1 lg in
begin
  have c₀ := ((univ_rpartrec α σ h').comp $
    (rcomputable.cond hc (rcomputable.const e) (rcomputable.const i)).pair rcomputable.id),
  simp at c₀,
  exact (c₀.of_eq $ λ x, by cases c x; simp[hg, hf] )
end

theorem bool_to_roption (c : α → bool):
  (λ a, cond (c a) (some 0) none : α →. ℕ) partrec_in (c : α →. bool) :=
rpartrec.cond rcomputable.refl (rcomputable.const 0) partrec.none.to_rpart

theorem universal_index {f : β → option τ} : ∃ u, ∀ x (y : α),
  (⟦u⟧^f (x, y) : roption σ) = ⟦x⟧^f y :=
by rcases rpartrec_univ_iff.mp (univ_rpartrec α σ f) with ⟨u, hu⟩; exact ⟨u, by simp[hu]⟩

theorem recursion (α σ) [primcodable α] [inhabited α] [primcodable σ] (f : β → option τ) :
  ∃ fixpoint : ℕ → ℕ, primrec fixpoint ∧
  (∀ {I : ℕ → ℕ} {i}, ⟦i⟧^f = (I : ℕ →. ℕ) → (⟦fixpoint i⟧^f : α →. σ) = ⟦I (fixpoint i)⟧^f) :=
begin
  have : ∃ t', ⟦t'⟧^f = λ (a : ℕ × α), (⟦a.1⟧^f a.1).bind (λ (x : ℕ), ⟦x⟧^f a.2),
  { have this := ((univ_rpartrec ℕ ℕ f).comp (fst.pair fst).to_comp.to_rcomp).bind
      ((univ_rpartrec α σ f).comp (snd.pair (snd.comp primrec.fst)).to_comp.to_rcomp),
    exact rpartrec_univ_iff.mp this },
  rcases this with ⟨t', lmm_t'⟩,
  let t : ℕ → ℕ := curry t',
  have : ∃ j, ⟦j⟧^f = λ (a : ℕ × ℕ), ⟦a.1⟧^f (t a.2),
  { have : computable t := curry_prim.to_comp.comp (computable.const t') computable.id,
    have := (univ_rpartrec _ ℕ f).comp (rcomputable.fst.pair (this.to_rcomp.comp rcomputable.snd)),
    exact rpartrec_univ_iff.mp this },
  rcases this with ⟨j, lmm_j⟩,
  let fixpoint : ℕ → ℕ := λ x, t (curry j x),
  have : primrec fixpoint := curry_prim.comp (primrec.const t')
    (curry_prim.comp (primrec.const j) primrec.id),
  refine ⟨fixpoint, this, _⟩,
  assume I i h, funext x,
  show ⟦fixpoint i⟧^f x = ⟦I (fixpoint i)⟧^f x,
  simp[fixpoint, lmm_t', lmm_j, h, t]
end

theorem recursion1 (α σ) [primcodable α] [inhabited α] [primcodable σ]
  {f : β → option τ} {I : ℕ → ℕ} (h : I computable_in (λ x, f x)) :
  ∃ n, (⟦n⟧^f : α →. σ) = ⟦I n⟧^f :=
by rcases recursion α σ f with ⟨fixpoint, cf, hfix⟩;
   rcases rpartrec_univ_iff.mp h with ⟨i, hi⟩;
   exact ⟨fixpoint i, hfix hi⟩

end rpartrec