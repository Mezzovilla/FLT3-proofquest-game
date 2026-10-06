import Game.Metadata
import Game.Levels.ThirdCyclotomicExtensions.L01_Units_mem

World "ThirdCyclotomicExtensions"
Level 2

Title "Units.not_exists_int_three_dvd_sub"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $m \\in \\Z$. \\\\\\\\
Then $3 \\notdivides \\eta - m$.
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
Let $m \in \Z$. \\\\
Then $3 \notdivides \eta - m$. -/
TheoremDoc IsCyclotomicExtension.Rat.Three.Units.not_exists_int_three_dvd_sub as "Units.not_exists_int_three_dvd_sub" in "Third Cyclotomic Extensions"

Statement Units.not_exists_int_three_dvd_sub : ¬(∃ n : ℤ, (3 : 𝓞 K) ∣ (η - n : 𝓞 K)) := by
  Hint "By properties of cyclotomic fields, we know that $\\set\u007b1,\\eta\u007d$ is an integral power basis of $\\cc\u007bO\u007d_K$
(see \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/FLT3/Mathlib/NumberTheory/Cyclotomic/Rat.html#IsPrimitiveRoot.integralPowerBasis'\u007d\u007bthis lemma\u007d,
\\href\u007bhttps://pitmonticone.github.io/FLT3/docs/FLT3/Mathlib/NumberTheory/Cyclotomic/Rat.html#IsPrimitiveRoot.power_basis_int'_dim\u007d\u007bthis lemma\u007d
and \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/FLT3/Mathlib/NumberTheory/Cyclotomic/Rat.html#IsPrimitiveRoot.integralPowerBasis'_gen\u007d\u007bthis lemma\u007d
which have already been formalised and included in Mathlib).\\\\
For every $\\xi \\in \\cc\u007bO\u007d_K$, we define $\\pi_1(\\xi)$ and $\\pi_2(\\xi)$ to be the first and second
coordinates of $\\xi$ with respect to the basis $\\set\u007b1,\\eta\u007d \\in \\cc\u007bO\u007d_K$, i.e.
$$\\xi = \\pi_1(\\xi) + \\pi_2(\\xi)\\eta.$$
By contradiction we assume that
$$\\exists m \\in \\Z \\text\u007b such that \u007d 3 \\divides \\eta - m,$$
which implies that
$$\\exists x \\in \\cc\u007bO\u007d_K \\text\u007b such that \u007d \\eta - m = 3 x.$$
By linearity of $\\pi_2$,
$$\\pi_2(\\eta) = \\pi_2(3x + m) = 3\\pi_2(x) + \\pi_2(m).$$
Since $\\pi_2(\\eta) = 1$ and $\\pi_2(m) = 0$, then we have that $3 \\divides 1$, which is a contradiction."
  intro ⟨n, x, h⟩
  let pB := hζ.integralPowerBasis'
  have hdim : pB.dim = 2 := by
    simp only [_root_.IsPrimitiveRoot.power_basis_int'_dim, PNat.val_ofNat, Nat.reduceSucc, pB]
    rfl
  replace hdim : 1 < pB.dim := by simp [hdim]
  rw [sub_eq_iff_eq_add] at h
  replace h := pB.basis.ext_elem_iff.1 h ⟨1, hdim⟩
  have := pB.basis_eq_pow ⟨1, hdim⟩
  rw [hζ.integralPowerBasis'_gen] at this
  simp only [PowerBasis.coe_basis, pow_one] at this
  rw [← this, show pB.gen = pB.gen ^ (⟨1, hdim⟩: Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.repr_self_apply] at h
  simp only [↓reduceIte, map_add, Finsupp.coe_add, Pi.add_apply] at h
  rw [show (3 : 𝓞 K) * x = (3 : ℤ) • x by simp, ← pB.basis.coord_apply,
    LinearMap.map_smul, ← zsmul_one, ← pB.basis.coord_apply, LinearMap.map_smul,
    show 1 = pB.gen ^ (⟨0, by linarith⟩: Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.coord_apply, pB.basis.coord_apply, pB.basis.repr_self_apply] at h
  simp only [smul_eq_mul, Fin.mk.injEq, zero_ne_one, ↓reduceIte, mul_zero, add_zero] at h
  have hdvd : ¬ ((3 : ℤ) ∣ 1) := by norm_num
  apply hdvd
  exact ⟨_, h⟩

NewTactic «show» linarith norm_num exact
NewDefinition IsPrimitiveRoot.integralPowerBasis IsPrimitiveRoot.integralPowerBasis'
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end IsCyclotomicExtension.Rat.Three

end

Conclusion "Level completed! 🎉"
