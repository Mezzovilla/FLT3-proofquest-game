import Game.Metadata
import Game.Levels.Preliminaries.L03_cube_of_castHom_ne_zero

World "ThirdCyclotomicExtensions"
Level 1

Title "Units.mem"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $u \\in \\cc{O}^\\times_K$ be a unit. \\\\\\\\
Then $u \\in \\set{1, -1, \\eta, -\\eta, \\eta^2, -\\eta^2}$.
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
Then $u \in \set{1, -1, \eta, -\eta, \eta^2, -\eta^2}$. -/
TheoremDoc IsCyclotomicExtension.Rat.Three.Units.mem as "Units.mem" in "Third Cyclotomic Extensions"

Statement Units.mem : ↑u ∈({1, -1, η, -η, η ^ 2, -η ^ 2} : Set (𝓞 K)) := by
  Hint "Let $\\cc\u007bF\u007d$ be the fundamental system of $K$. \\\\
By properties of cyclotomic fields, we know that $\\rank\u007bK\u007d = 0$
(see \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/Mathlib/NumberTheory/NumberField/Embeddings.html#NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces\u007d\u007bthis lemma\u007d,
\\href\u007bhttps://pitmonticone.github.io/FLT3/docs/FLT3/Mathlib/NumberTheory/Cyclotomic/Embeddings.html#IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero\u007d\u007bthis lemma\u007d
and \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/FLT3/Mathlib/NumberTheory/Cyclotomic/Embeddings.html#IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two\u007d\u007bthis lemma\u007d
which have already been formalised and included in Mathlib).
By the Dirichlet Unit Theorem (see \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/Mathlib/NumberTheory/NumberField/Units.html#NumberField.Units.exist_unique_eq_mul_prod\u007d\u007bMathlib\u007d),
we know that
$$\\exists x \\in K \\text\u007b with finite order, such that \u007d u = x \\prod_\u007bv\\in\\cc\u007bF\u007d\u007d v,$$
but since $\\rank\u007bK\u007d = 0$, then $\\cc\u007bF\u007d = \\emptyset$, which implies that $u = x$.\\\\
Since $u = x$ has finite order, by properties of primitive roots
(see \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.html#IsPrimitiveRoot.exists_pow_or_neg_mul_pow_of_isOfFinOrder\u007d\u007bthis lemma\u007d
that has already been formalised and included in Mathlib), we can deduce that
$$\\exists r < 3 \\text\u007b such that \u007d u = \\eta^r \\lor u = -\\eta^r.$$
Therefore, we can conclude
$$u \\in \\setb\u007b\\pm \\eta^r\u007d\u007br \\in \\set\u007b0,1,2\u007d\u007d = \\set\u007b1, -1, \\eta, -\\eta, \\eta^2, -\\eta^2\u007d.$$"
  have hrank : _root_.NumberField.Units.rank K = 0 := by
    dsimp [_root_.NumberField.Units.rank]
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, _root_.IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) K (by decide),
      zero_add, _root_.IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 3)]
    rfl
  obtain ⟨x, ⟨_, hxu, -⟩, -⟩ := _root_.NumberField.Units.exist_unique_eq_mul_prod _ u
  replace hxu : u = x := by
    rw [← mul_one x.1]
    rw [hxu]
    apply congr_arg
    rw [← Finset.prod_empty]
    congr
    rw [Finset.univ_eq_empty_iff, hrank]
    infer_instance
  obtain ⟨n, hnpos, hn⟩ := isOfFinOrder_iff_pow_eq_one.1 <| (CommGroup.mem_torsion _ _).1 x.2
  replace hn : (↑u : K) ^ ((⟨n, hnpos⟩ : ℕ+) : ℕ) = 1 := by
    norm_cast
    simp [hxu, hn]
  have hodd : Odd ((3 : ℕ+) : ℕ) := by decide
  obtain ⟨r, hr3, hru⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hodd
    (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hnpos, hn⟩)
  replace hr : r ∈ Finset.Ico 0 3 := Finset.mem_Ico.2 ⟨by simp, hr3⟩
  replace hru : ↑u = η ^ r ∨ ↑u = -η ^ r := by
    rcases hru with (h | h)
    · left; ext; exact h
    · right; ext; exact h
  fin_cases hr
  · rcases hru with (h | h)
    · simp only [h, pow_zero, Set.mem_insert_iff, eq_neg_self_iff, one_ne_zero,
      Set.mem_singleton_iff, false_or, true_or]
    · simp only [h, pow_zero, Set.mem_insert_iff, neg_eq_self_iff, one_ne_zero, neg_inj,
      Set.mem_singleton_iff, true_or, or_true]
  · rcases hru with (h | h)
    · simp only [h, zero_add, pow_one, Set.mem_insert_iff, eq_neg_self_iff, Set.mem_singleton_iff,
      true_or, or_true]
    · simp only [h, zero_add, pow_one, Set.mem_insert_iff, neg_inj, neg_eq_self_iff,
      Set.mem_singleton_iff, true_or, or_true]
  · rcases hru with (h | h)
    · apply Set.mem_insert_of_mem; apply Set.mem_insert_of_mem; simp [h]
    · apply Set.mem_insert_of_mem; apply Set.mem_insert_of_mem; simp [h]

NewTactic «have» dsimp rfl apply congr infer_instance norm_cast rcases left right
NewDefinition NumberField.Units.torsion NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115 NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118 NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129 NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132 NumberField.Units.rank NumberField.Units.dirichletUnitTheorem.w₀ NumberField.Units.dirichletUnitTheorem.logEmbedding NumberField.Units.unitLattice NumberField.Units.instDiscrete_unitLattice NumberField.Units.dirichletUnitTheorem.seq NumberField.Units.instZlattice_unitLattice NumberField.Units.unitLatticeEquiv NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510 NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513 NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519 NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532 NumberField.Units.basisModTorsion NumberField.Units.fundSystem
NewTheorem isOfFinOrder_iff_pow_eq_one CommGroup.mem_torsion Finset.mem_Ico Set.mem_insert_of_mem
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end IsCyclotomicExtension.Rat.Three

end

Conclusion "Level completed! 🎉"
