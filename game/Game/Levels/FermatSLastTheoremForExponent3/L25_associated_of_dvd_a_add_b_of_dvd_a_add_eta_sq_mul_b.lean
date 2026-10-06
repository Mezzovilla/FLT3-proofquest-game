import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L24_associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b

World "FermatSLastTheoremForExponent3"
Level 25

Title "associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S=(a, b, c, u)$ be a $solution$.\\\\
Let $p \\in \\cc{O}_K$ be a prime such that $p \\divides a+b$
and $p \\divides a+\\eta^2  b$.\\\\\\\\
Then $p$ is associated with $\\lambda$.
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
Let $S=(a, b, c, u)$ be a $solution$.\\
Let $p \in \cc{O}_K$ be a prime such that $p \divides a+b$
and $p \divides a+\eta^2  b$.\\\\
Then $p$ is associated with $\lambda$. -/
TheoremDoc Solution.associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b as "associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b" in "Fermat's Last Theorem for Exponent 3"

Statement associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b {p : 𝓞 K} (hp : Prime p)
  (hpab : p ∣ (S.a + S.b)) (hpaetasqb : p ∣ (S.a + η ^ 2 * S.b)) : Associated p λ := by
  Hint "We proceed by analysis each case:
\\begin\u007bitemize\u007d
\\item Case $p \\divides \\lambda$. It directly follows from *lmm:lambda_prime*.
\\item Case $p \\notdivides \\lambda$. \\\\
By hypothesis, we have that $p \\divides a+ b$ and $p \\divides a+\\eta^2 b$.
By *lmm:toInteger_cube_eq_one* and *lmm:eta_isUnit*, we have that
$$p \\divides \\eta ((a+\\eta^2 b) - (a+ b)) = - (\\eta^3 - \\eta) b = \\lambda b,$$
which implies that $p \\divides b$
and we proceed analogously to show that $p \\divides a$.\\\\
Therefore $p \\divides \\gcd(a,b)=1$ which is absurd.
\\end\u007bitemize\u007d
Therefore, we can conclude that $p$ is associated with $\\lambda$."
  by_cases p_lam : (p ∣ λ)
  · exact hp.associated_of_dvd _root_.hζ.lambda_prime p_lam
  have pdivb : p ∣ S.b := by
    have fgh : p ∣ λ * S.b := by
      rw [show λ * S.b = - (1 - η) * S.b by ring, ← _root_.hζ.toInteger_cube_eq_one]
      rw [show - (η ^ 3 - η) * S.b = η * ((S.a + S.b) - (S.a + η ^ 2 * S.b)) by ring]
      rw [_root_.hζ.eta_isUnit.dvd_mul_left]
      exact hpab.sub hpaetasqb
    exact hp.dvd_or_dvd fgh |>.resolve_left p_lam
  have pdiva : p ∣ S.a := by
    have fgh : p ∣ λ * S.a := by
      rw [show λ * S.a = - (1 - η) * S.a by ring, ← _root_.hζ.toInteger_cube_eq_one]
      rw [show - (η ^ 3 - η) * S.a = η * ((S.a + η ^ 2 * S.b) - η ^ 2 * (S.a + S.b)) by ring]
      rw [_root_.hζ.eta_isUnit.dvd_mul_left]
      exact hpaetasqb.sub (dvd_mul_of_dvd_right hpab _)
    exact hp.dvd_or_dvd fgh |>.resolve_left p_lam
  have punit := S.coprime.isUnit_of_dvd' pdiva pdivb
  exact hp.not_unit punit |>.elim

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
