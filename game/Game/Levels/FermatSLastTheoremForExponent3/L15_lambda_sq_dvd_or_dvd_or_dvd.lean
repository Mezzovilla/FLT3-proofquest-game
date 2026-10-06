import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L14_cube_add_cube_eq_mul

World "FermatSLastTheoremForExponent3"
Level 15

Title "lambda_sq_dvd_or_dvd_or_dvd"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S'=(a, b, c, u)$ be a $solution'$.\\\\\\\\
Then $(\\lambda^2 \\divides a + b) \\lor (\\lambda^2 \\divides a +
\\eta b) \\lor (\\lambda^2 \\divides a + \\eta^2 b)$.
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
open PartENat

/-- Let $K = \Q(\zeta_3)$ be the third cyclotomic field. \\
Let $\cc{O}_K = \Z[\zeta_3]$ be the ring of integers of $K$. \\
Let $\cc{O}^\times_K$ be the group of units of $\cc{O}_K$. \\
Let $\zeta_3 \in K$ be any primitive third root of unity. \\
Let $\eta \in \cc{O}_K$ be the element corresponding to $\zeta_3 \in K$. \\
Let $\lambda \in \cc{O}_K$ be such that $\lambda = \eta -1$. \\
Let $S'=(a, b, c, u)$ be a $solution'$.\\\\
Then $(\lambda^2 \divides a + b) \lor (\lambda^2 \divides a +
\eta b) \lor (\lambda^2 \divides a + \eta^2 b)$. -/
TheoremDoc lambda_sq_dvd_or_dvd_or_dvd as "lambda_sq_dvd_or_dvd_or_dvd" in "Fermat's Last Theorem for Exponent 3"

Statement lambda_sq_dvd_or_dvd_or_dvd :
    λ ^ 2 ∣ S.a + S.b ∨ λ ^ 2 ∣ S.a + η * S.b ∨ λ ^ 2 ∣ S.a + η ^ 2 * S.b := by
  Hint "By contradiction we assume that
$$(\\lambda^2 \\notdivides a + b) \\land (\\lambda^2 \\notdivides a +
\\eta b) \\land (\\lambda^2 \\notdivides a + \\eta^2 b).$$
Then, by definition, the multiplicity of $\\lambda$ in $a + b$, in $a +
\\eta b$ and in $a + \\eta^2 b$ is less than $2$.
By properties of divisibility, *lmm:lambda_pow_two_dvd_c* and *lmm:cube_add_cube_eq_mul*,
we have that
$$\\lambda^6 \\divides u c^3 = a^3 + b^3 = (a + b) (a + \\eta b) (a + \\eta^2 b).$$
Then, the multiplicity of $\\lambda$ in $(a + b) (a + \\eta b) (a + \\eta^2 b)$ is greater than
or equal to $6$. \\\\
By *lmm:lambda_prime* $\\lambda$ is prime, so we have that the multiplicity of $\\lambda$
in $(a + b) (a + \\eta b) (a + \\eta^2 b)$ is the sum of the multiplicities of $\\lambda$ in
$a + b$, in $a + \\eta b$ and in $a + \\eta^2 b$, which is less than $6$.
This is a contradiction that forces us to conclude that
$$(\\lambda^2 \\divides a + b) \\lor (\\lambda^2 \\divides a +
\\eta b) \\lor (\\lambda^2 \\divides a + \\eta^2 b).$$"
  classical
  by_contra! h
  rcases h with ⟨h1, h2, h3⟩
  rw [← multiplicity.multiplicity_lt_iff_not_dvd] at h1 h2 h3
  have h1' : multiplicity.Finite (_root_.hζ.toInteger - 1) (S.a + S.b) :=
    multiplicity.ne_top_iff_finite.1 (fun ht ↦ by simp [ht] at h1)
  have h2' : multiplicity.Finite (_root_.hζ.toInteger - 1) (S.a + η * S.b) :=
    multiplicity.ne_top_iff_finite.1 (fun ht ↦ by simp [ht] at h2)
  have h3' : multiplicity.Finite (_root_.hζ.toInteger - 1) (S.a + η ^ 2 * S.b) :=
    multiplicity.ne_top_iff_finite.1 (fun ht ↦ by simp [ht] at h3)
  replace h1' : (multiplicity (_root_.hζ.toInteger - 1) (S.a + S.b)).get h1' =
    multiplicity (_root_.hζ.toInteger - 1) (S.a + S.b) := by simp
  replace h2' : (multiplicity (_root_.hζ.toInteger - 1) (S.a + η * S.b)).get h2' =
    multiplicity (_root_.hζ.toInteger - 1) (S.a + η * S.b) := by simp
  replace h3' : (multiplicity (_root_.hζ.toInteger - 1) (S.a + η ^ 2 * S.b)).get h3' =
    multiplicity (_root_.hζ.toInteger - 1) (S.a + η ^ 2 * S.b) := by simp
  rw [← h1', coe_lt_coe] at h1; rw [← h2', coe_lt_coe] at h2; rw [← h3', coe_lt_coe] at h3
  have := (pow_dvd_pow_of_dvd (_root_.lambda_pow_two_dvd_c S) 3).mul_left S.u
  rw [← pow_mul, ← S.H, _root_.cube_add_cube_eq_mul, multiplicity.pow_dvd_iff_le_multiplicity,
    multiplicity.mul _root_.hζ.zeta_sub_one_prime', multiplicity.mul (_root_.IsPrimitiveRoot.lambda_prime _root_.hζ), ← h1', ← h2',
    ← h3', ← Nat.cast_add, ← Nat.cast_add, coe_le_coe] at this
  linarith

NewTactic by_contra
NewTheorem multiplicity.ne_top_iff_finite pow_dvd_pow_of_dvd
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
