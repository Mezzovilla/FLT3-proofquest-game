import Game.Metadata
import Game.Levels.ThirdCyclotomicExtensions.L19_cube_sub_one

World "ThirdCyclotomicExtensions"
Level 20

Title "lambda_dvd_mul_sub_one_mul_sub_eta_add_one"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $x \\in \\cc{O}_K$. \\\\\\\\
Then $\\lambda \\divides x(x - 1)(x - (\\eta + 1))$.
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
Let $\lambda \in \cc{O}_K$ be such that $\lambda = \eta -1$. \\
Let $x \in \cc{O}_K$. \\\\
Then $\lambda \divides x(x - 1)(x - (\eta + 1))$. -/
TheoremDoc IsCyclotomicExtension.Rat.Three.lambda_dvd_mul_sub_one_mul_sub_eta_add_one as "lambda_dvd_mul_sub_one_mul_sub_eta_add_one" in "Third Cyclotomic Extensions"

Statement lambda_dvd_mul_sub_one_mul_sub_eta_add_one (x : 𝓞 K) :
    λ ∣ x * (x - 1) * (x - (η + 1)) := by
  Hint "By *lmm:dvd_or_dvd_sub_one_or_dvd_add_one*, we have that
$$(\\lambda \\divides x) \\lor (\\lambda \\divides x-1) \\lor (\\lambda \\divides x+1).$$
We proceed by analysing each case:
\\begin\u007bitemize\u007d
\\item Case $\\lambda \\divides x$. \\\\
By properties of divisibility, we have that
$\\lambda \\divides x(x - 1)(x - (\\eta + 1))$.
\\item Case $\\lambda \\divides x-1$. \\\\
By properties of divisibility, we have that
$\\lambda \\divides x(x - 1)(x - (\\eta + 1))$.
\\item Case $\\lambda \\divides x+1$.\\\\
By properties of divisibility, it suffices to prove that
$$\\lambda \\divides x - (\\eta + 1) = x + 1 - (\\eta - 1 + 3).$$
By definition of $\\lambda$, we have that
$$x + 1 - (\\eta - 1 + 3) = x + 1 - (\\lambda + 3).$$
By properties of divisibility and *lmm:lambda_dvd_three*, we can deduce that
$\\lambda \\divides \\lambda + 3$.\\\\
Therefore, by properties of divisibility, we can conclude that
$$\\lambda \\divides x(x - 1)(x - (\\eta + 1)).$$
\\end\u007bitemize\u007d"
  rcases _root_.IsCyclotomicExtension.Rat.Three.dvd_or_dvd_sub_one_or_dvd_add_one hζ x with (h | h | h)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
  · refine dvd_mul_of_dvd_right ?_ _
    rw [show x - (η + 1) = x + 1 - (η - 1 + 3) by ring]
    exact dvd_sub h (dvd_add dvd_rfl <| _root_.IsCyclotomicExtension.Rat.Three.lambda_dvd_three hζ)

NewTheorem dvd_mul_of_dvd_left dvd_mul_of_dvd_right dvd_sub dvd_add dvd_rfl
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end IsCyclotomicExtension.Rat.Three

end

Conclusion "Level completed! 🎉"
