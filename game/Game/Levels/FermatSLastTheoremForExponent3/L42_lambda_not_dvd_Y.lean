import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L41_lambda_not_dvd_X

World "FermatSLastTheoremForExponent3"
Level 42

Title "lambda_not_dvd_Y"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S$ be a $solution$.\\\\\\\\
Then $\\lambda \\notdivides Y$.
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

/-- Let $K = \Q(\zeta_3)$ be the third cyclotomic field. \\
Let $\cc{O}_K = \Z[\zeta_3]$ be the ring of integers of $K$. \\
Let $\cc{O}^\times_K$ be the group of units of $\cc{O}_K$. \\
Let $\zeta_3 \in K$ be any primitive third root of unity. \\
Let $\eta \in \cc{O}_K$ be the element corresponding to $\zeta_3 \in K$. \\
Let $\lambda \in \cc{O}_K$ be such that $\lambda = \eta -1$. \\
Let $S$ be a $solution$.\\\\
Then $\lambda \notdivides Y$. -/
TheoremDoc Solution.lambda_not_dvd_Y as "lambda_not_dvd_Y" in "Fermat's Last Theorem for Exponent 3"

Statement lambda_not_dvd_Y : ¬ λ ∣ S.Y := by
  Hint "By contradiction we assume that $\\lambda \\divides Y$, then, by the properties of divisibility,
$\\lambda \\divides u_2 Y^3$, which implies, by *$u_1,u_2,u_3,X,Y,Z$*,
that $\\lambda \\divides y$.
However, this contradicts *lmm:lambda_not_dvd_y*
forcing us to conclude that $\\lambda \\notdivides Y$."
  intro h
  have hyp := dvd_mul_of_dvd_right h (S.u₂ * S.Y^2)
  rw [show ↑(_root_.Solution.u₂ S) * _root_.Solution.Y S ^ 2 * _root_.Solution.Y S = ↑S.u₂ * S.Y^3 by ring] at hyp
  rw [← _root_.Solution.u₂_Y_spec] at hyp
  apply _root_.Solution.lambda_not_dvd_y S
  simp [hyp]

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
