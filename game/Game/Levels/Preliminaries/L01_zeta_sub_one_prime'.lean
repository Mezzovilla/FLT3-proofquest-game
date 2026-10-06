import Game.Metadata

World "Preliminaries"
Level 1

Title "zeta_sub_one_prime'"

Introduction "
Let $p \\in \\N$ be prime. \\\\\\\\
If $\\zeta_p$ is a primitive $p$-th root of unity, then $\\zeta_p - 1$ is prime.
"

namespace IsCyclotomicExtension
end IsCyclotomicExtension

namespace NumberField
end NumberField

namespace IsCyclotomicExtension.Rat
end IsCyclotomicExtension.Rat

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'

/-- Let $p \in \N$ be prime. \\\\
If $\zeta_p$ is a primitive $p$-th root of unity, then $\zeta_p - 1$ is prime. -/
TheoremDoc IsPrimitiveRoot.zeta_sub_one_prime' as "zeta_sub_one_prime'" in "Preliminaries"

Statement zeta_sub_one_prime' [h : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    Prime ((hζ.toInteger - 1)) := by
  Hint "This has already been formalised and included in \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/FLT3/Mathlib/NumberTheory/Cyclotomic/Rat.html#IsPrimitiveRoot.zeta_sub_one_prime'\u007d\u007bMathlib\u007d."
  convert _root_.IsPrimitiveRoot.zeta_sub_one_prime (k := 0) (by simpa)
  simpa

NewTactic simpa
NewDefinition IsPrimitiveRoot.adjoinEquivRingOfIntegers IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers IsPrimitiveRoot.toInteger IsPrimitiveRoot.adjoinEquivRingOfIntegers' IsCyclotomicExtension.ring_of_integers'
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end IsPrimitiveRoot

end

Conclusion "Level completed! 🎉"
