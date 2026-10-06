import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L21_lambda_sq_not_dvd_a_add_eta_mul_b

World "FermatSLastTheoremForExponent3"
Level 22

Title "lambda_sq_not_dvd_a_add_eta_sq_mul_b"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S=(a, b, c, u)$ be a $solution$.\\\\\\\\
Then $\\lambda^2 \\notdivides a + \\eta^2  b$.
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
Let $S=(a, b, c, u)$ be a $solution$.\\\\
Then $\lambda^2 \notdivides a + \eta^2  b$. -/
TheoremDoc Solution.lambda_sq_not_dvd_a_add_eta_sq_mul_b as "lambda_sq_not_dvd_a_add_eta_sq_mul_b" in "Fermat's Last Theorem for Exponent 3"

Statement lambda_sq_not_dvd_a_add_eta_sq_mul_b : ¬ λ ^ 2 ∣ (S.a + η ^ 2 * S.b) := by
  Hint "By contradiction using *lmm:toInteger_eval_cyclo*, we assume
$\\lambda^2 \\divides a +\\eta^2 b = a + b -b + \\eta^2  b$.
Since $\\lambda^2 \\divides a+b$, then $\\lambda^2 \\divides b (\\eta^2 -1)
= \\lambda b (\\eta + 1)$. Since $\\lambda \\notdivides b$, then
$\\lambda \\divides \\eta+1 = \\lambda +2$, then $\\lambda \\divides 2$ which is absurd."
  intro h
  apply S.hb
  rcases h with ⟨k, hk⟩
  rw [show S.a + η ^ 2 * S.b = S.a + S.b - S.b + η ^ 2 * S.b by ring] at hk
  rcases S.hab with ⟨k', hk'⟩
  use (k - k') * (-η)
  rw [hk'] at hk
  rw [show λ ^ 2 * k' - S.b + η ^ 2 * S.b = λ * (S.b * (η +1) + λ * k') by ring,
    pow_two, mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, _root_.IsCyclotomicExtension.Rat.Three.lambda_ne_zero, or_false] at hk
  replace hk := congr_arg (fun x => x * (-η)) hk
  simp only at hk
  rw [show (S.b * (η + 1) + λ * k') * -η = (- S.b) * (η ^ 2 + η + 1 - 1) - η * λ * k' by ring] at hk
  rw [_root_.hζ.toInteger_eval_cyclo] at hk
  simp only [zero_sub, mul_neg, mul_one, neg_neg] at hk
  rw [sub_eq_iff_eq_add] at hk
  rw [hk]
  ring

NewTactic use
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
