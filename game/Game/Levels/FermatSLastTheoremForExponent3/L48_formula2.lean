import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L47_u₅'_isUnit
import Game.Generated.DefsAfter073

World "FermatSLastTheoremForExponent3"
Level 48

Title "formula2"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S$ be a $solution$ with multiplicity $n$.\\\\\\\\
Then $Y^3 + u_4 Z^3 = u_5 (\\lambda^(n-1) X)^3$.
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
Let $S$ be a $solution$ with multiplicity $n$.\\\\
Then $Y^3 + u_4 Z^3 = u_5 (\lambda^(n-1) X)^3$. -/
TheoremDoc Solution.formula2 as "formula2" in "Fermat's Last Theorem for Exponent 3"

Statement formula2 : S.Y ^ 3 + S.u₄ * S.Z ^ 3 = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3 := by
  Hint "Using *lmm:eta_isUnit*, *lmm:lambda_ne_zero*, it suffices to show that
$$\\lambda \\eta u_2 (Y^3 + u_4 Z^3) = \\lambda \\eta u_2 u_5 (\\lambda^(n-1) X)^3$$
which can be proved by simple calculations involving *lmm:toInteger_cube_eq_one*,
*lmm:Solution_two_le_multiplicity* and *lmm:formula1*."
  simp_rw [_root_.Solution.u₄, _root_.Solution.u₅, IsUnit.unit_spec]
  unfold _root_.Solution.u₄'
  unfold _root_.Solution.u₅'
  apply mul_left_cancel₀ S.u₂.isUnit.ne_zero
  apply mul_left_cancel₀ _root_.hζ.eta_isUnit.ne_zero
  apply mul_left_cancel₀ (_root_.IsCyclotomicExtension.Rat.Three.lambda_ne_zero _root_.hζ)
  rw [show λ * (η * (↑(_root_.Solution.u₂ S) * (_root_.Solution.Y S ^ 3 + η * ↑(_root_.Solution.u₃ S) * ↑(_root_.Solution.u₂ S)⁻¹ * _root_.Solution.Z S ^ 3)))
    = λ * η * ↑(_root_.Solution.u₂ S) * _root_.Solution.Y S ^ 3 + λ * η^2 * ↑(_root_.Solution.u₂ S) * ↑(_root_.Solution.u₂ S)⁻¹ * ↑(_root_.Solution.u₃ S) * _root_.Solution.Z S ^ 3 by ring]
  rw [show λ * (η * (↑(_root_.Solution.u₂ S) * (-η ^ 2 * ↑(_root_.Solution.u₁ S) * ↑(_root_.Solution.u₂ S)⁻¹
    * (λ ^ (S.multiplicity - 1) * _root_.Solution.X S) ^ 3)))
    = λ * (↑(_root_.Solution.u₂ S) * ↑(_root_.Solution.u₂ S)⁻¹ * (-η ^ 3 * ↑(_root_.Solution.u₁ S) * (λ ^ (S.multiplicity - 1) * _root_.Solution.X S) ^ 3)) by ring]
  rw [← sub_eq_zero]
  simp only [Units.mul_inv_cancel_right, Units.mul_inv, neg_mul, mul_neg, one_mul, sub_neg_eq_add]
  rw [_root_.hζ.toInteger_cube_eq_one, one_mul]
  have tmp : λ * (↑(_root_.Solution.u₁ S) * (λ ^ (S.multiplicity - 1) * _root_.Solution.X S) ^ 3)
      = ↑(_root_.Solution.u₁ S) * _root_.Solution.X S ^ 3 * λ ^ (3 * S.multiplicity - 2) := by
    rw [mul_comm, mul_assoc, mul_assoc]
    congr 1
    rw [mul_pow, mul_comm, ← mul_assoc, mul_comm _ (S.X ^ _)]
    congr 1
    rw [← pow_mul', ← pow_succ']
    congr 1
    have := _root_.Solution.two_le_multiplicity S
    omega
  rw [tmp]
  convert _root_.Solution.formula1 S using 1
  ring

NewDefinition Solution.u₄ Solution.u₅
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
