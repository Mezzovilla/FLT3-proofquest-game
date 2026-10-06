import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L10_lambda_pow_four_dvd_c_cube

World "FermatSLastTheoremForExponent3"
Level 11

Title "lambda_pow_two_dvd_c"

Introduction "
Let $S'=(a, b, c, u)$ be a $solution'$. \\\\\\\\
Then $\\lambda^2 \\divides c$.
"

namespace NumberField
end NumberField

namespace IsCyclotomicExtension.Rat.Three
end IsCyclotomicExtension.Rat.Three

section
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532
attribute [local instance] _root_.IsCyclotomicExtension.Rat.Three._instance_m464c54332e4379636c6f_l177
attribute [local instance] _root_.IsCyclotomicExtension.Rat.Three._instance_m464c54332e4379636c6f_l283
attribute [local instance] _root_.IsCyclotomicExtension.Rat.Three._instance_m464c54332e4379636c6f_l286
attribute [local instance 10000] _root_.Ring.toNeg
attribute [local instance 10000] _root_.Ring.toAddCommGroup
attribute [local instance 10000] _root_.NeZero.one
open NumberField
open nonZeroDivisors
open IsCyclotomicExtension.Rat.Three
open scoped Classical
attribute [local instance] _root_.IsCyclotomicExtension.Rat.three_pid
local notation "K" => CyclotomicField 3 ℚ
attribute [local instance] _root_._instance_m464c54332e464c5433_l154
attribute [-instance] _root_.ValuationRing.instIsBezoutToRing
attribute [local instance] _root_._instance_m464c54332e464c5433_l161
attribute [local instance] _root_._instance_m464c54332e464c5433_l163
local notation "η" => _root_.hζ.toInteger
local notation "λ" => η - 1
variable (S : _root_.Solution')

/-- Let $S'=(a, b, c, u)$ be a $solution'$. \\\\
Then $\lambda^2 \divides c$. -/
TheoremDoc lambda_pow_two_dvd_c as "lambda_pow_two_dvd_c" in "Fermat's Last Theorem for Exponent 3"

Statement lambda_pow_two_dvd_c : λ ^ 2 ∣ S.c := by
  Hint "Apply *lmm:lambda_pow_four_dvd_c_cube*."
  classical
  have  hm := S.multiplicity_lambda_c_finite
  suffices 2 ≤ (multiplicity ((_root_.hζ.toInteger - 1)) S.c).get hm by
    obtain ⟨x, hx⟩ := multiplicity.pow_multiplicity_dvd hm
    refine ⟨λ ^ ((multiplicity ((_root_.hζ.toInteger - 1)) S.c).get hm - 2) * x, ?_⟩
    rw [← mul_assoc, ← pow_add]
    convert hx using 3
    simp [this]
  have := _root_.lambda_pow_four_dvd_c_cube S
  have hm1 :(multiplicity (_root_.hζ.toInteger - 1) (S.c ^ 3)).get
    (multiplicity.finite_pow _root_.hζ.lambda_prime hm) =
    multiplicity (_root_.hζ.toInteger - 1) (S.c ^ 3) := by simp
  rw [multiplicity.pow_dvd_iff_le_multiplicity, ← hm1, multiplicity.pow' _root_.hζ.lambda_prime hm,
    Nat.cast_ofNat, Nat.ofNat_le_cast] at this
  linarith

NewTheorem multiplicity.pow_multiplicity_dvd
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
