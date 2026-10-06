import Game.Metadata
import Game.Levels.ThirdCyclotomicExtensions.L03_lambda_sq

World "ThirdCyclotomicExtensions"
Level 4

Title "eq_one_or_neg_one_of_unit_of_congruent"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $u \\in \\cc{O}^\\times_K$ be a unit. \\\\\\\\
If $\\exists m \\in \\Z$ such that $\\lambda^2 \\divides u - m$, then
$u = 1 \\lor u = -1$. \\\\
This is a special case of the Kummer's Lemma.
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

/-- Let $K = \Q(\zeta_3)$ be the third cyclotomic field. \\
Let $\cc{O}_K = \Z[\zeta_3]$ be the ring of integers of $K$. \\
Let $\cc{O}^\times_K$ be the group of units of $\cc{O}_K$. \\
Let $\zeta_3 \in K$ be any primitive third root of unity. \\
Let $\eta \in \cc{O}_K$ be the element corresponding to $\zeta_3 \in K$. \\
Let $\lambda \in \cc{O}_K$ be such that $\lambda = \eta -1$. \\
Let $u \in \cc{O}^\times_K$ be a unit. \\\\
If $\exists m \in \Z$ such that $\lambda^2 \divides u - m$, then
$u = 1 \lor u = -1$. \\
This is a special case of the Kummer's Lemma. -/
TheoremDoc IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent as "eq_one_or_neg_one_of_unit_of_congruent" in "Third Cyclotomic Extensions"

Statement eq_one_or_neg_one_of_unit_of_congruent (hcong : ∃ n : ℤ, λ ^ 2 ∣ (u - n : 𝓞 K)) :
    u = 1 ∨ u = -1 := by
  Hint "By *lmm:lambda_sq*, we have that $-3\\eta = \\lambda^2 \\divides u - m$, which implies that
$3 \\divides u - m$.\\\\
By *thm:mem*, we know that $u \\in \\set\u007b1, -1, \\eta, -\\eta, \\eta^2, -\\eta^2\u007d$. \\\\
We proceed by analysing each case:
\\begin\u007bitemize\u007d
\\item Case $u = 1 \\lor u = -1$. This finishes the proof.
\\item Case $u = \\eta$.\\\\
Since $3 \\divides u - m$, we have that $3 \\divides \\eta - m$, which contradicts
*thm:not_exists_int_three_dvd_sub* forcing us to conclude that $u \\neq \\eta$.
\\item Case $u = -\\eta$.\\\\
Since $3 \\divides u - m$, we have that $3 \\divides - \\eta - m$, then by properties of
divisibility $3 \\divides \\eta + m$, which contradicts
*thm:not_exists_int_three_dvd_sub* forcing us to conclude that $u \\neq -\\eta$.
\\item Case $u = \\eta^2$.\\\\
Since $3 \\divides u - m$, we have that $3 \\divides \\eta^2 - m$, which contradicts
*thm:not_exists_int_three_dvd_sub* since $\\eta^2$ is a third root of unity
(see \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/Mathlib/RingTheory/RootsOfUnity/Basic.html#IsPrimitiveRoot.pow_of_coprime\u007d\u007bMathlib\u007d),
forcing us to conclude that $u \\neq \\eta^2$.
\\item Case $u = -\\eta^2$.\\\\
Since $3 \\divides u - m$, we have that $3 \\divides - \\eta^2 - m$, then by properties of
divisibility $3 \\divides \\eta^2 + m$, which contradicts
*thm:not_exists_int_three_dvd_sub* since $\\eta^2$ is a third root of unity
(see \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/Mathlib/RingTheory/RootsOfUnity/Basic.html#IsPrimitiveRoot.pow_of_coprime\u007d\u007bMathlib\u007d),
forcing us to conclude that $u \\neq -\\eta^2$.
\\end\u007bitemize\u007d
Therefore, $u = 1 \\lor u = -1$."
  replace hcong : ∃ n : ℤ, (3 : 𝓞 K) ∣ (↑u - n : 𝓞 K) := by
    obtain ⟨n, x, hx⟩ := hcong
    exact ⟨n, -η * x, by rw [← mul_assoc, mul_neg, ← neg_mul, ← _root_.IsCyclotomicExtension.Rat.Three.lambda_sq, hx]⟩
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have := _root_.IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  have h2 : (hζ.pow_of_coprime 2 (by decide)).toInteger = hζ.toInteger ^ 2 := by ext; simp
  simp only [Set.mem_insert_iff, val_eq_one, Set.mem_singleton_iff] at this
  rcases this with (rfl | h | h | h | h | h)
  · left; rfl
  · right; ext; simp [h]
  · exfalso
    apply _root_.IsCyclotomicExtension.Rat.Three.Units.not_exists_int_three_dvd_sub hζ
    rw [← h]
    exact hcong
  · exfalso
    apply _root_.IsCyclotomicExtension.Rat.Three.Units.not_exists_int_three_dvd_sub hζ
    obtain ⟨n, x, hx⟩ := hcong
    rw [sub_eq_iff_eq_add] at hx
    refine ⟨-n, -x, ?_⟩
    rw [← neg_eq_iff_eq_neg.2 h, hx]
    simp
  · exfalso
    apply _root_.IsCyclotomicExtension.Rat.Three.Units.not_exists_int_three_dvd_sub <| hζ.pow_of_coprime 2 (by decide)
    rw [h2, ← h]
    exact hcong
  · exfalso
    apply _root_.IsCyclotomicExtension.Rat.Three.Units.not_exists_int_three_dvd_sub <| hζ.pow_of_coprime 2 (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    refine ⟨-n, -x, ?_⟩
    rw [h2, mul_neg, ← hx, ← neg_eq_iff_eq_neg.2 h]
    simp only [Int.cast_neg, sub_neg_eq_add, neg_sub]
    ring

NewTheorem mul_assoc mul_neg neg_mul IsCyclotomicExtension.zeta_spec
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end IsCyclotomicExtension.Rat.Three

end

Conclusion "Level completed! 🎉"
