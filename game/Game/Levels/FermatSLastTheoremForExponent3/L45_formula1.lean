import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L44_coprime_Y_Z

World "FermatSLastTheoremForExponent3"
Level 45

Title "formula1"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S$ be a $solution$ with multiplicity $n$.\\\\\\\\
Then $u_1 X^3 \\lambda^{3n-2}+u_2 \\eta Y^3 \\lambda +
u_3 \\eta^2 Z^3 \\lambda = 0$.
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
Then $u_1 X^3 \lambda^{3n-2}+u_2 \eta Y^3 \lambda +
u_3 \eta^2 Z^3 \lambda = 0$. -/
TheoremDoc Solution.formula1 as "formula1" in "Fermat's Last Theorem for Exponent 3"

Statement formula1 : S.u₁*S.X^3*λ^(3*S.multiplicity-2)+S.u₂*η*S.Y^3*λ+S.u₃*η^2*S.Z^3*λ = 0 := by
  Hint "Applying *$u_1,u_2,u_3,X,Y,Z$*,
*lmm:toInteger_cube_eq_one* and *lmm:toInteger_eval_cyclo*, we have
\\begin\u007balign*\u007d
u_1 X^3 \\lambda^\u007b3n-2\u007d+u_2 \\eta Y^3 \\lambda + u_3 \\eta^2 Z^3 \\lambda
&= x \\lambda^\u007b3n-2\u007d + \\eta y \\lambda + \\eta^2 z \\lambda \\\\
&= (a+b) + \\eta (a+\\eta b) + \\eta^2 (a+\\eta^2 b) \\\\
&= a (1 + \\eta + \\eta^2) + b (1 + \\eta^4 + \\eta^2) \\\\
&= (a+b)(1+\\eta+\\eta^2)\\\\
&= (a+b)0 = 0
\\end\u007balign*\u007d"
  rw [← _root_.Solution.u₁_X_spec, ← mul_comm η _, mul_assoc η _ _, ← _root_.Solution.u₂_Y_spec, ← mul_comm (η ^ 2) _, mul_assoc (η ^ 2) _ _, ← _root_.Solution.u₃_Z_spec]
  rw [mul_comm, mul_assoc, ← _root_.Solution.x_spec]
  rw [mul_comm, mul_comm _ λ, ← _root_.Solution.y_spec, mul_comm _ η]
  rw [mul_assoc, mul_comm _ λ, ← _root_.Solution.z_spec]
  rw [show S.a + S.b + η * (S.a + η * S.b) + η ^ 2 * (S.a + η ^ 2 * S.b) = S.a * (1 + η + η ^ 2) + S.b * (1 + (η ^ 3) * η + η ^ 2) by ring]
  rw [_root_.hζ.toInteger_cube_eq_one, one_mul, ← add_mul]
  convert mul_zero _
  convert _root_.hζ.toInteger_eval_cyclo using 1
  ring

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
