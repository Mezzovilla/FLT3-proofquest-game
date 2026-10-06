import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L33_coprime_x_z

World "FermatSLastTheoremForExponent3"
Level 34

Title "coprime_y_z"

Introduction "
Let $S$ be a $solution$.\\\\\\\\
Then $\\gcd(y, z) = 1$.
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
Then $\gcd(y, z) = 1$. -/
TheoremDoc Solution.coprime_y_z as "coprime_y_z" in "Fermat's Last Theorem for Exponent 3"

Statement coprime_y_z : IsCoprime S.y S.z := by
  Hint "Since $z \\neq 0$ by *lmm:lambda_not_dvd_z*, by the properties of PIDs it suffices to prove that
$\\forall p \\in \\cc\u007bO\u007d_K$ if $p$ is prime and $p \\divides y$, then $p \\notdivides z$.
Let $p \\in \\cc\u007bO\u007d_K$ be prime and suppose by contradiction that $p \\divides y$ and $p \\divides z$
which implies that $p \\divides \\lambda y = a+\\eta b$ and $p \\divides \\lambda z = a + \\eta^2 b$.
Then by *lmm:associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b*
we have that $p$ is associated with $\\lambda$, which implies that $\\lambda \\divides y$
that contradicts *lmm:lambda_not_dvd_y* forcing us to conclude that $p \\notdivides z$, which,
as stated above, implies that $\\gcd(y,z)=1$."
  apply isCoprime_of_prime_dvd
  . simp only [not_and]
    intro _ hz
    apply _root_.Solution.lambda_not_dvd_z S
    simp [hz]
  . intro p hp p_dvd_y p_dvd_z
    have aux1 := dvd_mul_of_dvd_right p_dvd_y (η - 1)
    rw [← _root_.Solution.y_spec] at aux1
    have aux2 := dvd_mul_of_dvd_right p_dvd_z (η - 1)
    rw [← _root_.Solution.z_spec] at aux2
    have aux3 : Associated p (η - 1) := by
      apply _root_.Solution.associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b
      exact hp
      exact aux1
      exact aux2
    have aux4 : λ ∣ S.y := by
      rw [← Associated.dvd_iff_dvd_left aux3]
      exact p_dvd_y
    apply _root_.Solution.lambda_not_dvd_y
    exact aux4

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
