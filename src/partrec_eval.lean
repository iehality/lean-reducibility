import computability.primrec
import computability.partrec
import computability.partrec_code
import computability.halting
import data.pfun
import tactic

open encodable denumerable roption

section code
open computable nat.partrec 

variables {α : Type*} {σ : Type*} {β : Type*} {τ : Type*} 
variables [primcodable α] [primcodable σ] [primcodable β] [primcodable τ]

lemma of_nat_code_surjective : ∀ c, ∃ e, code.of_nat_code e = c := surjective_decode_iget code

def eval (α σ) [primcodable α] [primcodable σ] (e : ℕ) : α →. σ := 
(λ a, ((code.of_nat_code e).eval (encode a)).bind (λ x, (decode σ x)))

notation `⟦`e`⟧₀`:max := eval _ _ e

theorem partrec.eval (α σ) [primcodable α] [primcodable σ] :
  partrec₂ (eval α σ) :=
(code.eval_part.comp 
  ((computable.of_nat code).comp fst) $ computable.encode.comp snd)
  .bind (computable.decode.comp snd).of_option

def evaln (α σ) [primcodable α] [primcodable σ] (s : ℕ) (e : ℕ) : α → option σ :=
(λ a, (code.evaln s (code.of_nat_code e) $ encode a).bind (λ x, decode σ x))

notation `⟦`e`⟧₀`:max` [`s`]` := evaln _ _ s e

theorem computable.evaln (α σ) [primcodable α] [primcodable σ] :
  computable₂ (λ x y, evaln α σ x.1 x.2 y : (ℕ × ℕ) → α → option σ) :=
have c₀ : computable (λ x, code.evaln x.1.1 (code.of_nat_code x.1.2) (encode x.2) : (ℕ × ℕ) × α → option ℕ) :=
  (code.evaln_prim.to_comp.comp $
    ((fst.comp fst).pair ((computable.of_nat code).comp $ snd.comp fst))
      .pair (computable.encode.comp snd)),
c₀.option_bind (computable.decode.comp snd)

def curry {α} [primcodable α] (e : ℕ) (n : α) : ℕ := encode (code.curry (code.of_nat_code e) (encode n))

theorem eval_curry (α β σ) [primcodable α] [primcodable β] [primcodable σ]
  (e n x) : eval α σ (curry e n) x = eval (β × α) σ e (n, x) :=
by simp[curry, eval, ←code.of_nat_code_eq]

theorem exists_index {f : α →. σ} :
  partrec f ↔ ∃ e, eval α σ e = f :=
begin
  simp[eval], split,
  { simp only [partrec,code.exists_code],
    rintros ⟨c, hc⟩,
    rcases of_nat_code_surjective c with ⟨e , ee⟩,
    use e, simp[ee,hc] },
  { rintros ⟨e, he⟩, rw ←he,
    have p : partrec (code.of_nat_code e).eval :=
      partrec.nat_iff.mpr (code.exists_code.mpr ⟨code.of_nat_code e, rfl⟩),
    exact (p.comp computable.encode).bind (computable.decode.comp snd).of_option }
end

theorem evaln_bound {s e x y} : evaln α σ s e x = some y → (encode x) < s :=
by { simp[evaln], intros z hz ez, exact code.evaln_bound hz }

theorem evaln_sound {s e x y} : evaln α σ s e x = some y → eval α σ e x = some y :=
by { rw roption.eq_some_iff, simp[eval, evaln],
     intros z hz ez, use z, exact ⟨code.evaln_sound hz,ez⟩ }

theorem evaln_complete {e : ℕ} {x : α} {y : σ} : 
  eval α σ e x = some y ↔ ∃ s, evaln α σ s e x = some y :=
begin
  rw roption.eq_some_iff,
  simp[eval, evaln], split,
  { rintros ⟨a, pa, ha⟩, rcases code.evaln_complete.mp pa with ⟨s, hs⟩,
    use s, use a, exact ⟨hs, ha⟩ },
  { rintros ⟨s, a, ha, ea⟩, use a, exact ⟨code.evaln_complete.mpr ⟨s, ha⟩, ea⟩ }
end

theorem evaln_complete_none {e x} :
  eval α σ e x = none ↔ ∀ s, evaln α σ s e x = none :=
begin
  split,
  { contrapose, simp, simp[←ne.def,option.ne_none_iff_exists],
    intros s y h, rw evaln_sound (show evaln α σ s e x = some y, by simp[h]),
    exact roption.some_ne_none _ },
  { contrapose, simp, simp[←ne.def,option.ne_none_iff_exists,ne_none_iff],
    intros y hy,
    rcases evaln_complete.mp hy with ⟨s, hs⟩, 
    use s, use y,
    simp[hs] }
end

theorem eval_bind_decode {e x} : 
  eval α σ e x = (eval α ℕ e x).bind (λ x, decode σ x):=
by simp[eval]

theorem evaln_bind_decode {s e x} : 
  evaln α σ s e x = (evaln α ℕ s e x).bind (λ x, decode σ x):=
by simp[evaln]; cases code.evaln s (code.of_nat_code e) (encode x); simp[(>>=)]

end code