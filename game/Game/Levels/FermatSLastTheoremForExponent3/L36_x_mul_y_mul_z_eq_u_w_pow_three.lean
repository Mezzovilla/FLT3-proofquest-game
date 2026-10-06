import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L35_mult_minus_two_plus_one_plus_one

World "FermatSLastTheoremForExponent3"
Level 36

Title "x_mul_y_mul_z_eq_u_w_pow_three"

Introduction "
Let $S=(a,b,c,u)$ be a $solution$.\\\\\\\\
Then $x y z = u w^3$.
"

namespace NumberField
end NumberField

namespace IsCyclotomicExtension.Rat.Three
end IsCyclotomicExtension.Rat.Three

section
open NumberField
open nonZeroDivisors
open IsCyclotomicExtension.Rat.Three
open scoped Classical

namespace Solution

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
attribute [local instance] _root_.IsCyclotomicExtension.Rat.three_pid
local notation "K" => CyclotomicField 3 ℚ
attribute [local instance] _root_._instance_m464c54332e464c5433_l154
attribute [-instance] _root_.ValuationRing.instIsBezoutToRing
attribute [local instance] _root_._instance_m464c54332e464c5433_l161
attribute [local instance] _root_._instance_m464c54332e464c5433_l163
local notation "η" => _root_.hζ.toInteger
local notation "λ" => η - 1
variable (S : _root_.Solution)

/-- Let $S=(a,b,c,u)$ be a $solution$.\\\\
Then $x y z = u w^3$. -/
TheoremDoc Solution.x_mul_y_mul_z_eq_u_w_pow_three as "x_mul_y_mul_z_eq_u_w_pow_three" in "Fermat's Last Theorem for Exponent 3"

Statement x_mul_y_mul_z_eq_u_w_pow_three : S.x * S.y * S.z = S.u * S.w ^ 3 := by
  Hint "It directly follows from *$y,z,w$*, *$x$*,
*lmm:cube_add_cube_eq_mul*,
*lmm:lambda_ne_zero*, *lmm:Solution_two_le_multiplicity* and
calculations using ring properties."
  suffices hh : λ ^ (3 * S.multiplicity - 2) * S.x * λ * S.y * λ * S.z = S.u * λ ^ (3 * S.multiplicity) * S.w ^ 3 by
    rw [show λ ^ (3 * S.multiplicity - 2) * _root_.Solution.x S * λ * _root_.Solution.y S * λ * _root_.Solution.z S = λ ^ (3 * S.multiplicity - 2) * λ * λ * _root_.Solution.x S * _root_.Solution.y S * _root_.Solution.z S by ring] at hh
    rw [mul_comm _ (λ ^ (3 * S.multiplicity))] at hh
    simp only [← pow_succ] at hh
    have := S.two_le_multiplicity
    have hhh : 3 * S.multiplicity - 2 + 1 + 1 = 3 * S.multiplicity := by
      omega
    rw [hhh] at hh
    rw [mul_assoc, mul_assoc, mul_assoc] at hh
    simp [_root_.IsCyclotomicExtension.Rat.Three.lambda_ne_zero] at hh
    convert hh using 1
    ring
  simp only [← _root_.Solution.x_spec, mul_assoc, ← _root_.Solution.y_spec, ← _root_.Solution.z_spec]
  simp only [mul_comm 3, pow_mul, ← mul_pow, ← _root_.Solution.w_spec]
  rw [← S.H, _root_.cube_add_cube_eq_mul]
  ring

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
