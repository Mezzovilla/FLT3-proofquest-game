import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L28_lambda_not_dvd_z

World "FermatSLastTheoremForExponent3"
Level 29

Title "lambda_pow_dvd_a_add_b"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S=(a, b, c, u)$ be a $solution$ with multiplicity $n$.\\\\\\\\
Then $\\lambda^{3n -2} \\divides a + b$.
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
Let $S=(a, b, c, u)$ be a $solution$ with multiplicity $n$.\\\\
Then $\lambda^{3n -2} \divides a + b$. -/
TheoremDoc Solution.lambda_pow_dvd_a_add_b as "lambda_pow_dvd_a_add_b" in "Fermat's Last Theorem for Exponent 3"

Statement lambda_pow_dvd_a_add_b : λ ^ (3 * S.multiplicity - 2) ∣ S.a + S.b := by
  Hint "By *Multiplicity of Solution* we have that $\\lambda^n \\divides c$.
Since $u$ is a unit, then by *lmm:cube_add_cube_eq_mul* we have that
$$\\lambda^\u007b3n\u007d \\divides u  c^3 = a^3 + b^3 = (a+b)(a + \\eta b)(a + \\eta^2 b)
= (a+b)(\\lambda y)(\\lambda z).$$
Then applying *lmm:lambda_not_dvd_y* and *lmm:lambda_not_dvd_z*, we can conclude
that $\\lambda^\u007b3n-2\u007d \\divides a+b$."
  have h : λ ^ S.multiplicity ∣ S.c  := multiplicity.pow_multiplicity_dvd _
  replace h := pow_dvd_pow_of_dvd h 3
  replace h : (λ ^ S.multiplicity) ^ 3 ∣ S.u * S.c ^ 3 := by simp [h]
  have := S.two_le_multiplicity
  have hh : 3 * S.multiplicity - 2 + 1 + 1 = 3 * S.multiplicity := by
    omega
  rw [← S.H, _root_.cube_add_cube_eq_mul, ← pow_mul,
    mul_comm, _root_.Solution.y_spec, _root_.Solution.z_spec, ← hh, pow_succ, pow_succ] at h
  apply _root_.hζ.lambda_prime.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_z
  apply _root_.hζ.lambda_prime.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_y
  rw [show (S.a + S.b) * (λ * _root_.Solution.y S) * (λ * _root_.Solution.z S) = (S.a + S.b) * _root_.Solution.y S * _root_.Solution.z S * λ * λ by ring] at h
  simp only [mul_dvd_mul_iff_right (_root_.IsCyclotomicExtension.Rat.Three.lambda_ne_zero _root_.hζ)] at h
  rwa [show (S.a + S.b) * _root_.Solution.y S * _root_.Solution.z S = _root_.Solution.y S * (_root_.Solution.z S * (S.a + S.b)) by ring] at h

NewTactic omega
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
