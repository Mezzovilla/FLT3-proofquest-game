import Game.Metadata
import Game.Levels.ThirdCyclotomicExtensions.L18_toInteger_eval_cyclo

World "ThirdCyclotomicExtensions"
Level 19

Title "cube_sub_one"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $x \\in \\cc{O}_K$. \\\\\\\\
Then $x^3 - 1 = (x - 1)(x - \\eta)(x - \\eta^ 2)$.
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
attribute [local instance] _root_.IsCyclotomicExtension.Rat.Three._instance_m464c54332e4379636c6f_l283
attribute [local instance] _root_.IsCyclotomicExtension.Rat.Three._instance_m464c54332e4379636c6f_l286
attribute [local instance 10000] _root_.Ring.toNeg
attribute [local instance 10000] _root_.Ring.toAddCommGroup
attribute [local instance 10000] _root_.NeZero.one

/-- Let $K = \Q(\zeta_3)$ be the third cyclotomic field. \\
Let $\cc{O}_K = \Z[\zeta_3]$ be the ring of integers of $K$. \\
Let $\cc{O}^\times_K$ be the group of units of $\cc{O}_K$. \\
Let $\zeta_3 \in K$ be any primitive third root of unity. \\
Let $\eta \in \cc{O}_K$ be the element corresponding to $\zeta_3 \in K$. \\
Let $x \in \cc{O}_K$. \\\\
Then $x^3 - 1 = (x - 1)(x - \eta)(x - \eta^ 2)$. -/
TheoremDoc IsCyclotomicExtension.Rat.Three.cube_sub_one as "cube_sub_one" in "Third Cyclotomic Extensions"

Statement cube_sub_one (x : 𝓞 K) : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2) := by
  Hint "Applying *lmm:toInteger_cube_eq_one* and *lmm:toInteger_eval_cyclo*, we have that
\\begin\u007balign*\u007d
(x - 1)(x - \\eta)(x - \\eta^ 2)
&= x^3 - x^2 (\\eta^2 + \\eta + 1) + x (\\eta^2 + \\eta + \\eta^3) - \\eta^3 \\\\
&= x^3 - x^2 (\\eta^2 + \\eta + 1) + x (\\eta^2 + \\eta + 1) - 1 \\\\
&= x^3 - 1.
\\end\u007balign*\u007d"
  symm
  calc _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + η ^ 3) - η ^ 3 := by ring
  _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + 1) - 1 := by rw [hζ.toInteger_cube_eq_one]
  _ = x ^ 3 - 1 := by rw [hζ.toInteger_eval_cyclo]; ring

NewTactic «calc»
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end IsCyclotomicExtension.Rat.Three

end

Conclusion "Level completed! 🎉"
