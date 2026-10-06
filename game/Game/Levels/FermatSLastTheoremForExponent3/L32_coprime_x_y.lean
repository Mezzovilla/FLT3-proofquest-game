import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L31_lambda_not_dvd_x

World "FermatSLastTheoremForExponent3"
Level 32

Title "coprime_x_y"

Introduction "
Let $S$ be a $solution$ with multiplicity $n$.\\\\\\\\
Then $\\gcd(x,y) = 1$.
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

/-- Let $S$ be a $solution$ with multiplicity $n$.\\\\
Then $\gcd(x,y) = 1$. -/
TheoremDoc Solution.coprime_x_y as "coprime_x_y" in "Fermat's Last Theorem for Exponent 3"

Statement coprime_x_y : IsCoprime S.x S.y := by
  Hint "Since $y \\neq 0$ by *lmm:lambda_not_dvd_y*, by the properties of PIDs it suffices to prove that
$\\forall p \\in \\cc\u007bO\u007d_K$ if $p$ is prime and $p \\divides x$, then $p \\notdivides y$.
Let $p \\in \\cc\u007bO\u007d_K$ be prime and suppose by contradiction that $p \\divides x$ and $p \\divides y$
which implies that $p \\divides \\lambda^\u007b3n-2\u007d x = a+b$ and $p \\divides \\lambda y = a + \\eta b$.
Then by *lmm:associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b*
we have that $p$ is associated with $\\lambda$, which implies that $\\lambda \\divides x$
that contradicts *lmm:lambda_not_dvd_x* forcing us to conclude that $p \\notdivides y$, which,
as stated above, implies that $\\gcd(x,y)=1$."
  apply isCoprime_of_prime_dvd
  · simp only [not_and]
    intro _  hy
    apply _root_.Solution.lambda_not_dvd_y S
    simp [hy]
  · intro p hp p_dvd_x p_dvd_y
    have aux1 := dvd_mul_of_dvd_right p_dvd_x (λ ^ (3 * S.multiplicity - 2))
    rw [← _root_.Solution.x_spec] at aux1
    have aux2 := dvd_mul_of_dvd_right p_dvd_y (η - 1)
    rw [← _root_.Solution.y_spec] at aux2
    have aux3 : Associated p (η - 1) := by
      apply _root_.Solution.associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b
      exact hp
      exact aux1
      exact aux2
    have aux4 : λ ∣ S.x := by
      rw [← Associated.dvd_iff_dvd_left aux3]
      exact p_dvd_x
    apply _root_.Solution.lambda_not_dvd_x
    exact aux4

NewTheorem isCoprime_of_prime_dvd
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
