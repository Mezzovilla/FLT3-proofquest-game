import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L30_lambda_not_dvd_w

World "FermatSLastTheoremForExponent3"
Level 31

Title "lambda_not_dvd_x"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S$ be a $solution$.\\\\\\\\
Then $\\lambda \\notdivides x$.
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
Then $\lambda \notdivides x$. -/
TheoremDoc Solution.lambda_not_dvd_x as "lambda_not_dvd_x" in "Fermat's Last Theorem for Exponent 3"

Statement lambda_not_dvd_x : ¬ λ ∣ S.x := by
  Hint "By contradiction, if $\\lambda \\divides x$, then
$\\lambda^\u007b3n-1\u007d \\divides \\lambda^\u007b3n-2\u007d  x = a+b$. Using *lmm:lambda_dvd_a_add_eta_mul_b*
and *lmm:lambda_dvd_a_add_eta_sq_mul_b*, we have that $\\lambda^\u007b3n+1\u007d \\divides
(a+b)  (a + \\eta  b)  (a + \\eta^2 cdot b) = a^3+b^3
= u c^3 = u \\lambda^\u007b3n\u007d w^3$.
Then $\\lambda \\divides w^3$ which implies that $\\lambda \\divides w$, that
contradicts *lmm:lambda_not_dvd_w* forcing us to conclude $\\lambda \\notdivides x$."
  intro h
  replace h := mul_dvd_mul_left (λ ^ (3 * S.multiplicity - 2)) h
  rw [mul_comm, ← _root_.Solution.x_spec] at h
  replace h := mul_dvd_mul (mul_dvd_mul h S.lambda_dvd_a_add_eta_mul_b) S.lambda_dvd_a_add_eta_sq_mul_b
  rw [← _root_.cube_add_cube_eq_mul, S.H, _root_.Solution.w_spec] at h
  simp only [Units.isUnit, IsUnit.dvd_mul_left] at h
  rw [← pow_succ', mul_comm, ← mul_assoc, ← pow_succ'] at h
  have := S.two_le_multiplicity
  have hh : 3 * S.multiplicity - 2 + 1 + 1 = 3 * S.multiplicity := by
    omega
  rw [hh, mul_pow, ← pow_mul, mul_comm _ 3, mul_dvd_mul_iff_left _] at h
  · replace h := Prime.dvd_of_dvd_pow _root_.hζ.lambda_prime h
    exact _root_.Solution.lambda_not_dvd_w _ h
  · simp [_root_.IsCyclotomicExtension.Rat.Three.lambda_ne_zero]

NewDefinition Solution.x
NewTheorem Prime.dvd_of_dvd_pow
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
