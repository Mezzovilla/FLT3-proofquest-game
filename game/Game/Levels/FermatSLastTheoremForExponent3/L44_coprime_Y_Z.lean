import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L43_lambda_not_dvd_Z

World "FermatSLastTheoremForExponent3"
Level 44

Title "coprime_Y_Z"

Introduction "
Let $S$ be a $solution$.\\\\\\\\
Then $\\gcd(Y, Z) = 1$.
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

/-- Let $S$ be a $solution$.\\\\
Then $\gcd(Y, Z) = 1$. -/
TheoremDoc Solution.coprime_Y_Z as "coprime_Y_Z" in "Fermat's Last Theorem for Exponent 3"

Statement coprime_Y_Z : IsCoprime S.Y S.Z := by
  Hint "Since $Z \\neq 0$ by *lmm:lambda_not_dvd_Z*, by the properties of PIDs it suffices to prove that
$\\forall p \\in \\cc\u007bO\u007d_K$ if $p$ is prime and $p \\divides Y$, then $p \\notdivides Z$.
Let $p \\in \\cc\u007bO\u007d_K$ be prime and suppose by contradiction that $p \\divides Y$ and $p \\divides Z$
which implies that $p \\divides u_2 Y^3 = y$ and $p \\divides \\lambda u_3 Z^3 = z$.
But this contradicts *lmm:coprime_y_z* forcing us to conclude that $p \\notdivides Z$, which,
as stated above, implies that $\\gcd(Y,Z)=1$."
  apply isCoprime_of_prime_dvd
  · simp only [not_and]
    intro _ hy_Z_zero
    apply _root_.Solution.lambda_not_dvd_Z S
    simp only [hy_Z_zero, dvd_zero]
  · intro p hp p_dvd_Y p_dvd_Z
    have auxY := dvd_mul_of_dvd_right p_dvd_Y (S.u₂ * S.Y^2)
    rw [show S.u₂ * S.Y^2 * S.Y = S.u₂ * S.Y^3 by ring] at auxY
    rw [← _root_.Solution.u₂_Y_spec] at auxY
    have auxZ := dvd_mul_of_dvd_right p_dvd_Z (S.u₃ * S.Z^2)
    rw [show S.u₃ * S.Z^2 * S.Z = S.u₃ * S.Z^3 by ring] at auxZ
    rw [← _root_.Solution.u₃_Z_spec] at auxZ
    have gcd_isUnit : IsUnit (gcd S.y S.z) := by
      rw [gcd_isUnit_iff S.y S.z]
      simp only [_root_.Solution.coprime_y_z]
    apply hp.not_unit
    refine isUnit_of_dvd_unit ?_ gcd_isUnit
    rw [dvd_gcd_iff]
    simp [auxY, auxZ]

NewTheorem isUnit_of_dvd_unit
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
