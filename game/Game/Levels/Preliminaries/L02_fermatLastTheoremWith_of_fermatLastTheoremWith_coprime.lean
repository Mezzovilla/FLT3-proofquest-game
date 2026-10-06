import Game.Metadata
import Game.Levels.Preliminaries.L01_zeta_sub_one_prime'

World "Preliminaries"
Level 2

Title "fermatLastTheoremWith_of_fermatLastTheoremWith_coprime"

Introduction "
Let $R$ be a commutative semiring, domain and normalised $\\gcd$ monoid.\\% ASK EXPERTS
Let $a, b, c \\in R$. \\\\
Let $n \\in \\N$. \\\\\\\\
Then, to prove Fermat's Last Theorem for exponent $n$ in $R$,
one can assume, without loss of generality, that $\\gcd(a,b,c)=1$.
"

section
open List
variable {α : Type*} [Semiring α] [NoZeroDivisors α] {m n : ℕ}
open Finset

/-- Let $R$ be a commutative semiring, domain and normalised $\gcd$ monoid.\% ASK EXPERTS
Let $a, b, c \in R$. \\
Let $n \in \N$. \\\\
Then, to prove Fermat's Last Theorem for exponent $n$ in $R$,
one can assume, without loss of generality, that $\gcd(a,b,c)=1$. -/
TheoremDoc fermatLastTheoremWith_of_fermatLastTheoremWith_coprime as "fermatLastTheoremWith_of_fermatLastTheoremWith_coprime" in "Preliminaries"

Statement fermatLastTheoremWith_of_fermatLastTheoremWith_coprime {n : ℕ} {R : Type*} [CommSemiring R]
    [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    (hn : ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → ({a, b, c} : Finset R).gcd id = 1 →
      a ^ n + b ^ n ≠ c ^ n) :
    _root_.FermatLastTheoremWith R n := by
  Hint "This has already been formalised and included in \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/FLT3/Mathlib/NumberTheory/FLT/Basic.html#fermatLastTheoremWith_of_fermatLastTheoremWith_coprime\u007d\u007bMathlib\u007d."
  intro a b c ha hb hc habc
  let s : Finset R := {a, b, c}; let d := s.gcd id
  obtain ⟨A, hA⟩ : d ∣ a := gcd_dvd (by simp [s])
  obtain ⟨B, hB⟩ : d ∣ b := gcd_dvd (by simp [s])
  obtain ⟨C, hC⟩ : d ∣ c := gcd_dvd (by simp [s])
  simp only [hA, hB, hC, mul_ne_zero_iff, mul_pow] at ha hb hc habc
  rw [← mul_add, mul_right_inj' (pow_ne_zero n ha.1)] at habc
  refine hn A B C ha.2 hb.2 hc.2 ?_ habc
  rw [← Finset.normalize_gcd, normalize_eq_one]
  obtain ⟨u, hu⟩ := normalize_associated d
  refine ⟨u, mul_left_cancel₀ (mt normalize_eq_zero.mp ha.1) (hu.symm ▸ ?_)⟩
  rw [← Finset.gcd_mul_left, gcd_eq_gcd_image, image_insert, image_insert, image_singleton,
      id_eq, id_eq, id_eq, ← hA, ← hB, ← hC]

NewTactic intro «let» obtain simp rw refine
NewDefinition FermatLastTheoremWith
NewTheorem Finset.gcd_dvd normalize_associated mul_left_cancel₀ normalize_eq_zero
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
