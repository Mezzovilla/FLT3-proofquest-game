import Game.Metadata
import Game.Levels.ThirdCyclotomicExtensions.L20_lambda_dvd_mul_sub_one_mul_sub_eta_add_one

World "ThirdCyclotomicExtensions"
Level 21

Title "lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $x \\in \\cc{O}_K$. \\\\\\\\
If $\\lambda\\divides x - 1$, then $\\lambda^ 4 \\divides x^3 - 1$.
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
If $\lambda\divides x - 1$, then $\lambda^ 4 \divides x^3 - 1$. -/
TheoremDoc IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one as "lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one" in "Third Cyclotomic Extensions"

Statement lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one {x : 𝓞 K} (h : λ ∣ x - 1) :
    λ ^ 4 ∣ x ^ 3 - 1 := by
  Hint "Let $\\lambda \\divides x - 1$, which is equivalent to say that
$$\\exists y\\in \\cc\u007bO\u007d_K \\text\u007b such that \u007d x - 1 = \\lambda y.$$
By ring properties and *lmm:cube_sub_one*, we have that
$$x^3 - 1 = \\lambda^3 (y (y - 1) (y - (\\eta + 1))).$$
By properties of divisibility and *lmm:lambda_dvd_mul_sub_one_mul_sub_eta_add_one*,
we can conclude that $$\\lambda^ 4 \\divides x^3 - 1.$$"
  obtain ⟨y, hy⟩ := h
  have : x ^ 3 - 1 = λ ^ 3 * (y * (y - 1) * (y - (η + 1))) := by
    calc _ =  (x - 1) * (x - 1 - λ) * (x - 1 - λ * (η + 1)) := by rw [_root_.IsCyclotomicExtension.Rat.Three.cube_sub_one hζ x]; ring
    _ = _ := by rw [hy]; ring
  rw [this, show λ ^ 4 = λ ^ 3 * λ by ring]
  exact mul_dvd_mul dvd_rfl (_root_.IsCyclotomicExtension.Rat.Three.lambda_dvd_mul_sub_one_mul_sub_eta_add_one hζ y)

NewTheorem mul_dvd_mul
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end IsCyclotomicExtension.Rat.Three

end

Conclusion "Level completed! 🎉"
