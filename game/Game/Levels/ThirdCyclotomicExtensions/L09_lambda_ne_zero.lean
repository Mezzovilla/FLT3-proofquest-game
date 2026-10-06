import Game.Metadata
import Game.Levels.ThirdCyclotomicExtensions.L08_lambda_prime

World "ThirdCyclotomicExtensions"
Level 9

Title "lambda_ne_zero"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\\\\\
Then $\\lambda \\neq 0$.
"

namespace NumberField
end NumberField

namespace NumberField.Units
end NumberField.Units

section
open NumberField
open Units
open InfinitePlace
open nonZeroDivisors
open Polynomial

namespace IsCyclotomicExtension.Rat.Three

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
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ ↑(3 : ℕ+)) (u : (𝓞 K)ˣ)
local notation "η" => hζ.toInteger
local notation "λ" => hζ.toInteger - 1
attribute [local instance] _root_.IsCyclotomicExtension.Rat.Three._instance_m464c54332e4379636c6f_l177

/-- Let $K = \Q(\zeta_3)$ be the third cyclotomic field. \\
Let $\cc{O}_K = \Z[\zeta_3]$ be the ring of integers of $K$. \\
Let $\cc{O}^\times_K$ be the group of units of $\cc{O}_K$. \\
Let $\zeta_3 \in K$ be any primitive third root of unity. \\
Let $\eta \in \cc{O}_K$ be the element corresponding to $\zeta_3 \in K$. \\
Let $\lambda \in \cc{O}_K$ be such that $\lambda = \eta -1$. \\\\
Then $\lambda \neq 0$. -/
TheoremDoc IsCyclotomicExtension.Rat.Three.lambda_ne_zero as "lambda_ne_zero" in "Third Cyclotomic Extensions"

Statement lambda_ne_zero : λ ≠ 0 := by
  Hint "It directly follows from *lmm:lambda_prime* since zero is not prime."
  exact hζ.lambda_prime.ne_zero

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end IsCyclotomicExtension.Rat.Three

end

Conclusion "Level completed! 🎉"
