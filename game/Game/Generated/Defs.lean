import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.TFAE
import Mathlib.Data.ZMod.Basic
import GameServer.Commands

namespace IsCyclotomicExtension
end IsCyclotomicExtension

namespace NumberField
end NumberField

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat

namespace IsCyclotomicExtension.Rat

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]

theorem discr_prime_pow_eq_unit_mul_pow' [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    ∃ (u : ℤˣ) (n : ℕ), discr ℚ (hζ.subOnePowerBasis ℚ).basis = u * p ^ n := by
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm]
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (p ^ k).pos)

/-- Definition `IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow'`. -/
DefinitionDoc IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow' as "discr_prime_pow_eq_unit_mul_pow'"

end IsCyclotomicExtension.Rat

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat

namespace IsCyclotomicExtension.Rat

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]

theorem isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  refine' ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, _⟩, rfl⟩, _⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        (le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure (hζ.isIntegral (p ^ k).pos)) _)
  let B := hζ.subOnePowerBasis ℚ
  have hint : IsIntegral ℤ B.gen := (hζ.isIntegral (p ^ k).pos).sub isIntegral_one
-- Porting note: the following `haveI` was not needed because the locale `cyclotomic` set it
-- as instances.
  letI := IsCyclotomicExtension.finiteDimensional {p ^ k} ℚ K
  have H := discr_mul_isIntegral_mem_adjoin ℚ hint h
  obtain ⟨u, n, hun⟩ := _root_.IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow' hζ
  rw [hun] at H
  replace H := Subalgebra.smul_mem _ H u.inv
-- Porting note: the proof is slightly different because of coercions.
  rw [← smul_assoc, ← smul_mul_assoc, Units.inv_eq_val_inv, zsmul_eq_mul, ← Int.cast_mul,
    Units.inv_mul, Int.cast_one, one_mul, smul_def, map_pow] at H
  cases k
  · haveI : IsCyclotomicExtension {1} ℚ K := by simpa using hcycl
    have : x ∈ (⊥ : Subalgebra ℚ K) := by
      rw [singleton_one ℚ K]
      exact mem_top
    obtain ⟨y, rfl⟩ := mem_bot.1 this
    replace h := (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).1 h
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hz, ← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ _
  · have hmin : (minpoly ℤ B.gen).IsEisensteinAt (Submodule.span ℤ {((p : ℕ) : ℤ)}) := by
      have h₁ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp (cyclotomic.irreducible_rat (p ^ _).pos)
      rw [IsPrimitiveRoot.subOnePowerBasis_gen] at h₁
      rw [h₁, ← map_cyclotomic_int, show Int.castRingHom ℚ = algebraMap ℤ ℚ by rfl,
        show X + 1 = map (algebraMap ℤ ℚ) (X + 1) by simp, ← map_comp] at h₂
      haveI : CharZero ℚ := StrictOrderedSemiring.to_charZero
      rw [IsPrimitiveRoot.subOnePowerBasis_gen,
        map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int h₂]
      exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p _
    refine'
      adjoin_le _
        (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (n := n)
          (Nat.prime_iff_prime_int.1 hp.out) hint h (by simpa using H) hmin)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)

/-- Definition `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow`. -/
DefinitionDoc IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow as "isIntegralClosure_adjoin_singleton_of_prime_pow"

end IsCyclotomicExtension.Rat

end

namespace IsCyclotomicExtension.Rat
end IsCyclotomicExtension.Rat

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]

@[simps!]
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegers
    [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  let _ := _root_.IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  IsIntegralClosure.equiv ℤ (adjoin ℤ ({ζ} : Set K)) K (𝓞 K)

/-- Definition `IsPrimitiveRoot.adjoinEquivRingOfIntegers`. -/
DefinitionDoc IsPrimitiveRoot.adjoinEquivRingOfIntegers as "adjoinEquivRingOfIntegers"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]

def IsCyclotomicExtension.ringOfIntegers [IsCyclotomicExtension {p ^ k} ℚ K] :
    IsCyclotomicExtension {p ^ k} ℤ (𝓞 K) := let _ := (zeta_spec (p ^ k) ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec (p ^ k) ℚ K).adjoinEquivRingOfIntegers

/-- Definition `IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers`. -/
DefinitionDoc IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers as "IsCyclotomicExtension.ringOfIntegers"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers

noncomputable def integralPowerBasis [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (p ^ k).pos)).map hζ.adjoinEquivRingOfIntegers

/-- Definition `IsPrimitiveRoot.integralPowerBasis`. -/
DefinitionDoc IsPrimitiveRoot.integralPowerBasis as "integralPowerBasis"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers

abbrev toInteger {k : ℕ+} (hζ : IsPrimitiveRoot ζ k) : 𝓞 K := ⟨ζ, hζ.isIntegral k.pos⟩

-- Porting note: the proof changed because `simp` unfolds too much.

/-- Definition `IsPrimitiveRoot.toInteger`. -/
DefinitionDoc IsPrimitiveRoot.toInteger as "toInteger"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers

@[simp]
theorem integralPowerBasis_gen [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    hζ.integralPowerBasis.gen = hζ.toInteger :=
  Subtype.ext <| show algebraMap _ K hζ.integralPowerBasis.gen = _ by
    rw [_root_.IsPrimitiveRoot.integralPowerBasis, PowerBasis.map_gen, adjoin.powerBasis'_gen]
    simp only [adjoinEquivRingOfIntegers_apply, IsIntegralClosure.algebraMap_lift]
    rfl

/-- Definition `IsPrimitiveRoot.integralPowerBasis_gen`. -/
DefinitionDoc IsPrimitiveRoot.integralPowerBasis_gen as "integralPowerBasis_gen"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers

@[simps!]
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegers'
    [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  @_root_.IsPrimitiveRoot.adjoinEquivRingOfIntegers p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one])

/-- Definition `IsPrimitiveRoot.adjoinEquivRingOfIntegers'`. -/
DefinitionDoc IsPrimitiveRoot.adjoinEquivRingOfIntegers' as "adjoinEquivRingOfIntegers'"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers

def _root_.IsCyclotomicExtension.ring_of_integers' [IsCyclotomicExtension {p} ℚ K] :
    IsCyclotomicExtension {p} ℤ (𝓞 K) := let _ := (zeta_spec p ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec p ℚ K).adjoinEquivRingOfIntegers'

/-- Definition `IsCyclotomicExtension.ring_of_integers'`. -/
DefinitionDoc IsCyclotomicExtension.ring_of_integers' as "ring_of_integers'"

end IsPrimitiveRoot

end

namespace IsPrimitiveRoot
end IsPrimitiveRoot

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'
open nonZeroDivisors
open IsPrimitiveRoot
variable (K p k)

theorem absdiscr_prime_pow [NumberField K] [IsCyclotomicExtension {p ^ k} ℚ K] :
    NumberField.discr K =
    (-1) ^ ((p ^ k : ℕ).totient / 2) * p ^ ((p : ℕ) ^ (k - 1) * ((p - 1) * k - 1)) := by
  have hζ := (IsCyclotomicExtension.zeta_spec (p ^ k) ℚ K)
  let pB₁ := _root_.IsPrimitiveRoot.integralPowerBasis hζ
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ pB₁.basis, ← Algebra.discr_localizationLocalization ℤ ℤ⁰ K]
  convert IsCyclotomicExtension.discr_prime_pow hζ (cyclotomic.irreducible_rat (p ^ k).2) using 1
  · have : pB₁.dim = (IsPrimitiveRoot.powerBasis ℚ hζ).dim := by
      rw [← PowerBasis.finrank, ← PowerBasis.finrank]
      exact RingOfIntegers.rank K
    rw [← Algebra.discr_reindex _ _ (finCongr this)]
    congr 1
    ext i
    simp_rw [Function.comp_apply, Basis.localizationLocalization_apply, powerBasis_dim,
      PowerBasis.coe_basis, pB₁, _root_.IsPrimitiveRoot.integralPowerBasis_gen]
    convert ← ((IsPrimitiveRoot.powerBasis ℚ hζ).basis_eq_pow i).symm using 1
  · simp_rw [algebraMap_int_eq, map_mul, map_pow, map_neg, map_one, map_natCast]

/-- Definition `IsCyclotomicExtension.Rat.absdiscr_prime_pow`. -/
DefinitionDoc IsCyclotomicExtension.Rat.absdiscr_prime_pow as "absdiscr_prime_pow"

end IsCyclotomicExtension.Rat

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'
open nonZeroDivisors
open IsPrimitiveRoot
variable (K p k)
open Nat

theorem absdiscr_prime_pow_succ [NumberField K] [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] :
    NumberField.discr K =
    (-1) ^ ((p : ℕ) ^ k * (p - 1) / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using _root_.IsCyclotomicExtension.Rat.absdiscr_prime_pow p (k + 1) K

/-- Definition `IsCyclotomicExtension.Rat.absdiscr_prime_pow_succ`. -/
DefinitionDoc IsCyclotomicExtension.Rat.absdiscr_prime_pow_succ as "absdiscr_prime_pow_succ"

end IsCyclotomicExtension.Rat

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'
open nonZeroDivisors
open IsPrimitiveRoot
variable (K p k)

theorem absdiscr_prime [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    NumberField.discr K = (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    rw [zero_add, pow_one]
    infer_instance
  rw [_root_.IsCyclotomicExtension.Rat.absdiscr_prime_pow_succ p 0 K]
  simp only [Int.reduceNeg, pow_zero, one_mul, zero_add, mul_one, mul_eq_mul_left_iff, gt_iff_lt,
    Nat.cast_pos, PNat.pos, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and, or_false]
  rfl

/-- Definition `IsCyclotomicExtension.Rat.absdiscr_prime`. -/
DefinitionDoc IsCyclotomicExtension.Rat.absdiscr_prime as "absdiscr_prime"

end IsCyclotomicExtension.Rat

end

section
namespace IsCyclotomicExtension.Rat

open NumberField
open InfinitePlace
open FiniteDimensional
open Complex
open Nat
open Polynomial
variable {n : ℕ+} (K : Type u) [Field K] [CharZero K]

theorem nrRealPlaces_eq_zero [IsCyclotomicExtension {n} ℚ K]
    (hn : 2 < n) :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    NrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  apply (IsCyclotomicExtension.zeta_spec n ℚ K).nrRealPlaces_eq_zero_of_two_lt hn

/-- Definition `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`. -/
DefinitionDoc IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero as "nrRealPlaces_eq_zero"

end IsCyclotomicExtension.Rat

end

section
namespace IsCyclotomicExtension.Rat

open NumberField
open InfinitePlace
open FiniteDimensional
open Complex
open Nat
open Polynomial
variable {n : ℕ+} (K : Type u) [Field K] [CharZero K]
variable (n)

theorem nrComplexPlaces_eq_totient_div_two [h : IsCyclotomicExtension {n} ℚ K] :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    NrComplexPlaces K = φ n / 2 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  by_cases hn : 2 < n
  · obtain ⟨k, hk : φ n = k + k⟩ := totient_even hn
    have key := card_add_two_mul_card_eq_rank K
    rw [_root_.IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K hn, zero_add, IsCyclotomicExtension.finrank (n := n) K
      (cyclotomic.irreducible_rat n.pos), hk, ← two_mul, Nat.mul_right_inj (by norm_num)] at key
    simp [hk, key, ← two_mul]
  · have : φ n = 1 := by
      by_cases h1 : 1 < n.1
      · convert totient_two
        exact (eq_of_le_of_not_lt (succ_le_of_lt h1) hn).symm
      · convert totient_one
        rw [← PNat.one_coe, PNat.coe_inj]
        exact eq_of_le_of_not_lt (not_lt.mp h1) (PNat.not_lt_one _)
    rw [this]
    apply nrComplexPlaces_eq_zero_of_finrank_eq_one
    rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat n.pos), this]

/-- Definition `IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two`. -/
DefinitionDoc IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two as "nrComplexPlaces_eq_totient_div_two"

end IsCyclotomicExtension.Rat

end

section
namespace IsCyclotomicExtension.Rat

attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'
open NumberField
open Polynomial
open InfinitePlace
open Nat
open Real
open cyclotomic
variable (K : Type u) [Field K] [NumberField K]

theorem three_pid [IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [_root_.IsCyclotomicExtension.Rat.absdiscr_prime 3 K, IsCyclotomicExtension.finrank (n := 3) K
    (irreducible_rat (by norm_num)), _root_.IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3, totient_prime
      PNat.prime_three]
  simp only [Int.reduceNeg, PNat.val_ofNat, succ_sub_succ_eq_sub, tsub_zero, zero_lt_two,
    Nat.div_self, pow_one, cast_ofNat, neg_mul, one_mul, abs_neg, Int.cast_abs, Int.int_cast_ofNat,
    factorial_two, gt_iff_lt, abs_of_pos (show (0 : ℝ) < 3 by norm_num)]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

/-- Definition `IsCyclotomicExtension.Rat.three_pid`. -/
DefinitionDoc IsCyclotomicExtension.Rat.three_pid as "three_pid"

end IsCyclotomicExtension.Rat

end

namespace NumberField.Units
end NumberField.Units

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace

def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

/-- Definition `NumberField.Units.torsion`. -/
DefinitionDoc NumberField.Units.torsion as "torsion"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace

def _instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115 : Nonempty (_root_.NumberField.Units.torsion K) := One.instNonempty

/-- Definition `NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115`. -/
DefinitionDoc NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115 as "_instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]

theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ → K) :=
  fun _ _ h => by rwa [SetLike.coe_eq_coe, Units.eq_iff] at h

/-- Definition `NumberField.Units.coe_injective`. -/
DefinitionDoc NumberField.Units.coe_injective as "coe_injective"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
variable {K}

theorem coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : (↑(x ^ n) : K) = (x : K) ^ n := by
  rw [← SubmonoidClass.coe_pow, ← val_pow_eq_pow_val]

/-- Definition `NumberField.Units.coe_pow`. -/
DefinitionDoc NumberField.Units.coe_pow as "coe_pow"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
variable {K}

theorem coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl

/-- Definition `NumberField.Units.coe_one`. -/
DefinitionDoc NumberField.Units.coe_one as "coe_one"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace

theorem mem_torsion {x : (𝓞 K)ˣ} [NumberField K] :
    x ∈ _root_.NumberField.Units.torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, _root_.NumberField.Units.torsion, CommGroup.mem_torsion]
  refine ⟨fun hx φ ↦ (((φ.comp $ algebraMap (𝓞 K) K).toMonoidHom.comp $
    Units.coeHom _).isOfFinOrder hx).norm_eq_one, fun h ↦ isOfFinOrder_iff_pow_eq_one.2 ?_⟩
  obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.prop h
  exact ⟨n, hn, by ext; rw [_root_.NumberField.Units.coe_pow, hx, _root_.NumberField.Units.coe_one]⟩

/-- Definition `NumberField.Units.mem_torsion`. -/
DefinitionDoc NumberField.Units.mem_torsion as "mem_torsion"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115

def _instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118 [NumberField K] : Fintype (_root_.NumberField.Units.torsion K) := by
  refine @Fintype.ofFinite _ (Set.finite_coe_iff.mpr ?_)
  refine Set.Finite.of_finite_image ?_ ((_root_.NumberField.Units.coe_injective K).injOn _)
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((_root_.NumberField.Units.mem_torsion K).mp h_tors) φ)

-- a shortcut instance to stop the next instance from timing out

/-- Definition `NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118`. -/
DefinitionDoc NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118 as "_instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118

def _instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129 [NumberField K] : Finite (_root_.NumberField.Units.torsion K) := inferInstance

/-- Definition `NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129`. -/
DefinitionDoc NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129 as "_instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129

def _instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132 [NumberField K] : IsCyclic (_root_.NumberField.Units.torsion K) := subgroup_units_cyclic _

/-- Definition `NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132`. -/
DefinitionDoc NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132 as "_instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}

def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some

/-- Definition `NumberField.Units.dirichletUnitTheorem.w₀`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.w₀ as "w₀"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)

def logEmbedding : Additive ((𝓞 K)ˣ) →+ ({w : InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} → ℝ) :=
{ toFun := fun x w => mult w.val * Real.log (w.val ↑(Additive.toMul x))
  map_zero' := by simp; rfl
  map_add' := fun _ _ => by simp [Real.log_mul, mul_add]; rfl }

/-- Definition `NumberField.Units.dirichletUnitTheorem.logEmbedding`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.logEmbedding as "logEmbedding"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)

noncomputable def _root_.NumberField.Units.unitLattice :
    AddSubgroup ({w : InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} → ℝ) :=
  AddSubgroup.map (_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K) ⊤

/-- Definition `NumberField.Units.unitLattice`. -/
DefinitionDoc NumberField.Units.unitLattice as "unitLattice"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
variable {K}

theorem coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) ≠ 0 :=
  Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

/-- Definition `NumberField.Units.coe_ne_zero`. -/
DefinitionDoc NumberField.Units.coe_ne_zero as "coe_ne_zero"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl

/-- Definition `Rat.RingOfIntegers.isUnit_iff`. -/
DefinitionDoc Rat.RingOfIntegers.isUnit_iff as "Rat.RingOfIntegers.isUnit_iff"

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
variable (K : Type*) [Field K]
variable {K}

theorem NumberField.isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← _root_.Rat.RingOfIntegers.isUnit_iff]

/-- Definition `NumberField.isUnit_iff_norm`. -/
DefinitionDoc NumberField.isUnit_iff_norm as "NumberField.isUnit_iff_norm"

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}

theorem sum_logEmbedding_component (x : (𝓞 K)ˣ) :
    ∑ w, _root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K x w = - mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K)) := by
  have h := congr_arg Real.log (prod_eq_abs_norm (x : K))
  rw [show |(Algebra.norm ℚ) (x : K)| = 1 from _root_.NumberField.isUnit_iff_norm.mp x.isUnit, Rat.cast_one,
    Real.log_one, Real.log_prod] at h
  · simp_rw [Real.log_pow] at h
    rw [← insert_erase (mem_univ w₀), sum_insert (not_mem_erase w₀ univ), add_comm,
      add_eq_zero_iff_eq_neg] at h
    convert h using 1
    · refine (sum_subtype _ (fun w => ?_) (fun w => (mult w) * (Real.log (w (x : K))))).symm
      exact ⟨ne_of_mem_erase, fun h => mem_erase_of_ne_of_mem h (mem_univ w)⟩
    · norm_num
  · exact fun w _ => pow_ne_zero _ (AbsoluteValue.ne_zero _ (_root_.NumberField.Units.coe_ne_zero x))

/-- Definition `NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component as "sum_logEmbedding_component"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}

theorem logEmbedding_component_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K x‖ ≤ r)
    (w : {w : InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀}) : |_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K x w| ≤ r := by
  lift r to NNReal using hr
  simp_rw [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe] at h
  exact h w (mem_univ _)

/-- Definition `NumberField.Units.dirichletUnitTheorem.logEmbedding_component_le`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.logEmbedding_component_le as "logEmbedding_component_le"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}

@[simp]
theorem logEmbedding_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀}) :
    (_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K x) w = mult w.val * Real.log (w.val x) := rfl

/-- Definition `NumberField.Units.dirichletUnitTheorem.logEmbedding_component`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.logEmbedding_component as "logEmbedding_component"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}

theorem log_le_of_logEmbedding_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K x‖ ≤ r)
    (w : InfinitePlace K) : |Real.log (w x)| ≤ (Fintype.card (InfinitePlace K)) * r := by
  have tool : ∀ x : ℝ, 0 ≤ x → x ≤ mult w * x := fun x hx => by
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals { rw [mult]; split_ifs <;> norm_num }
  by_cases hw : w = _root_.NumberField.Units.dirichletUnitTheorem.w₀
  · have hyp := congr_arg (‖·‖) (_root_.NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component x).symm
    replace hyp := (le_of_eq hyp).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · rw [← hw]
      exact tool _ (abs_nonneg _)
    · refine (sum_le_card_nsmul univ _ _
        (fun w _ => _root_.NumberField.Units.dirichletUnitTheorem.logEmbedding_component_le hr h w)).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul ?_ le_rfl hr (Fintype.card (InfinitePlace K)).cast_nonneg
      simp [card_univ]
  · have hyp := _root_.NumberField.Units.dirichletUnitTheorem.logEmbedding_component_le hr h ⟨w, hw⟩
    rw [_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding_component, abs_mul, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · exact tool _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul (Nat.one_le_cast.mpr Fintype.card_pos) (le_of_eq rfl) hr (Nat.cast_nonneg _)

/-- Definition `NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le as "log_le_of_logEmbedding_le"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)

theorem unitLattice_inter_ball_finite (r : ℝ) :
    ((unitLattice K : Set ({ w : InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} → ℝ)) ∩
      Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_le r 0
  · convert Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices {x : (𝓞 K)ˣ | IsIntegral ℤ (x : K) ∧
        ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ Real.exp ((Fintype.card (InfinitePlace K)) * r)}.Finite by
      refine (Set.Finite.image (_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K) this).subset ?_
      rintro _ ⟨⟨x, ⟨_, rfl⟩⟩, hx⟩
      refine ⟨x, ⟨x.val.prop, (le_iff_le _ _).mp (fun w => (Real.log_le_iff_le_exp ?_).mp ?_)⟩, rfl⟩
      · exact pos_iff.mpr (_root_.NumberField.Units.coe_ne_zero x)
      · rw [mem_closedBall_zero_iff] at hx
        exact (le_abs_self _).trans (_root_.NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le hr hx w)
    refine Set.Finite.of_finite_image ?_ ((_root_.NumberField.Units.coe_injective K).injOn _)
    refine (Embeddings.finite_of_norm_le K ℂ
        (Real.exp ((Fintype.card (InfinitePlace K)) * r))).subset ?_
    rintro _ ⟨x, ⟨⟨h_int, h_le⟩, rfl⟩⟩
    exact ⟨h_int, h_le⟩

/-- Definition `NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite as "unitLattice_inter_ball_finite"

end NumberField.Units.dirichletUnitTheorem

end

namespace NumberField.Units.dirichletUnitTheorem
end NumberField.Units.dirichletUnitTheorem

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional

def instDiscrete_unitLattice : DiscreteTopology (_root_.NumberField.Units.unitLattice K) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by norm_num)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective _)
    convert _root_.NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite K 1
    ext x
    refine ⟨?_, fun ⟨hx1, hx2⟩ => ⟨⟨x, hx1⟩, hx2, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨Subtype.mem x, hx⟩

/-- Definition `NumberField.Units.instDiscrete_unitLattice`. -/
DefinitionDoc NumberField.Units.instDiscrete_unitLattice as "instDiscrete_unitLattice"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)
open NumberField.mixedEmbedding
open NNReal
attribute [-instance] _root_.FractionalIdeal.commSemiring
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

theorem seq_next {x : 𝓞 K} (hx : x ≠ 0) :
    ∃ y : 𝓞 K, y ≠ 0 ∧ (∀ w, w ≠ w₁ → w y < w x) ∧ |Algebra.norm ℚ (y : K)| ≤ B := by
  let f : InfinitePlace K → ℝ≥0 :=
    fun w => ⟨(w x) / 2, div_nonneg (AbsoluteValue.nonneg _ _) (by norm_num)⟩
  suffices ∀ w, w ≠ w₁ → f w ≠ 0 by
    obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
    obtain ⟨y, hy, h_ynz, h_yle⟩ := exists_ne_zero_mem_ringOfIntegers_lt (f := g)
      (by rw [convexBodyLT_volume]; convert hB; exact congr_arg ((↑): NNReal → ENNReal) h_gprod)
    refine ⟨⟨y, hy⟩, Subtype.ne_of_val_ne h_ynz, fun w hw => (h_geqf w hw ▸ h_yle w).trans ?_, ?_⟩
    · rw [← Rat.cast_le (K := ℝ), Rat.cast_natCast]
      calc
        _ = ∏ w : InfinitePlace K, w y ^ mult w := (prod_eq_abs_norm (y : K)).symm
        _ ≤ ∏ w : InfinitePlace K, (g w : ℝ) ^ mult w := by
          refine prod_le_prod ?_ ?_
          · exact fun _ _ => pow_nonneg (by positivity) _
          · exact fun w _ => pow_le_pow_left (by positivity) (le_of_lt (h_yle w)) (mult w)
        _ ≤ (B : ℝ) := by
          simp_rw [← NNReal.coe_pow, ← NNReal.coe_prod]
          exact le_of_eq (congr_arg toReal h_gprod)
    · refine div_lt_self ?_ (by norm_num)
      simp only [pos_iff, ne_eq, ZeroMemClass.coe_eq_zero, hx, not_false_eq_true]
  intro _ _
  rw [ne_eq, Nonneg.mk_eq_zero, div_eq_zero_iff, map_eq_zero, not_or, ZeroMemClass.coe_eq_zero]
  exact ⟨hx, by norm_num⟩

/-- Definition `NumberField.Units.dirichletUnitTheorem.seq_next`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.seq_next as "seq_next"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)
open NumberField.mixedEmbedding
open NNReal
attribute [-instance] _root_.FractionalIdeal.commSemiring
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

def seq : ℕ → { x : 𝓞 K // x ≠ 0 }
  | 0 => ⟨1, by norm_num⟩
  | n + 1 =>
    ⟨(_root_.NumberField.Units.dirichletUnitTheorem.seq_next K w₁ hB (seq n).prop).choose, (_root_.NumberField.Units.dirichletUnitTheorem.seq_next K w₁ hB (seq n).prop).choose_spec.1⟩

/-- Definition `NumberField.Units.dirichletUnitTheorem.seq`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.seq as "seq"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)
open NumberField.mixedEmbedding
open NNReal
attribute [-instance] _root_.FractionalIdeal.commSemiring
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

theorem seq_ne_zero (n : ℕ) : (seq K w₁ hB n : K) ≠ 0 := by
  refine (map_ne_zero_iff (algebraMap (𝓞 K) K) ?_).mpr (seq K w₁ hB n).prop
  exact IsFractionRing.injective { x // x ∈ 𝓞 K } K

/-- Definition `NumberField.Units.dirichletUnitTheorem.seq_ne_zero`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.seq_ne_zero as "seq_ne_zero"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)
open NumberField.mixedEmbedding
open NNReal
attribute [-instance] _root_.FractionalIdeal.commSemiring
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

theorem seq_decreasing {n m : ℕ} (h : n < m) (w : InfinitePlace K) (hw : w ≠ w₁) :
    w (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB m) < w (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB n) := by
  induction m with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero n h
  | succ m m_ih =>
      cases eq_or_lt_of_le (Nat.le_of_lt_succ h) with
      | inl hr =>
          rw [hr]
          exact (_root_.NumberField.Units.dirichletUnitTheorem.seq_next K w₁ hB (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB m).prop).choose_spec.2.1 w hw
      | inr hr =>
          refine lt_trans ?_ (m_ih hr)
          exact (_root_.NumberField.Units.dirichletUnitTheorem.seq_next K w₁ hB (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB m).prop).choose_spec.2.1 w hw

/-- Definition `NumberField.Units.dirichletUnitTheorem.seq_decreasing`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.seq_decreasing as "seq_decreasing"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)
open NumberField.mixedEmbedding
open NNReal
attribute [-instance] _root_.FractionalIdeal.commSemiring
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

theorem seq_norm_le (n : ℕ) :
    Int.natAbs (Algebra.norm ℤ (seq K w₁ hB n : 𝓞 K)) ≤ B := by
  cases n with
  | zero =>
      have : 1 ≤ B := by
        contrapose! hB
        simp only [Nat.lt_one_iff.mp hB, CharP.cast_eq_zero, mul_zero, zero_le]
      simp only [ne_eq, seq, map_one, Int.natAbs_one, this]
  | succ n =>
      rw [← Nat.cast_le (α := ℚ), Int.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
      exact (_root_.NumberField.Units.dirichletUnitTheorem.seq_next K w₁ hB (seq K w₁ hB n).prop).choose_spec.2.2

/-- Definition `NumberField.Units.dirichletUnitTheorem.seq_norm_le`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.seq_norm_le as "seq_norm_le"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)
open NumberField.mixedEmbedding
open NNReal
attribute [-instance] _root_.FractionalIdeal.commSemiring
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

theorem seq_norm_ne_zero (n : ℕ) : Algebra.norm ℤ (seq K w₁ hB n : 𝓞 K) ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr (Subtype.ne_of_val_ne (_root_.NumberField.Units.dirichletUnitTheorem.seq_ne_zero K w₁ hB n))

/-- Definition `NumberField.Units.dirichletUnitTheorem.seq_norm_ne_zero`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.seq_norm_ne_zero as "seq_norm_ne_zero"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)
open NumberField.mixedEmbedding
open NNReal
attribute [-instance] _root_.FractionalIdeal.commSemiring
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

theorem exists_unit (w₁ : InfinitePlace K) :
    ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K, w ≠ w₁ → Real.log (w u) < 0 := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, minkowskiBound K 1 < (convexBodyLTFactor K) * B := by
    conv => congr; ext; rw [mul_comm]
    exact ENNReal.exists_nat_mul_gt (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero K))
      (ne_of_lt (minkowskiBound_lt_top K 1))
  rsuffices ⟨n, m, hnm, h⟩ : ∃ n m, n < m ∧
      (Ideal.span ({ (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB n : 𝓞 K) }) = Ideal.span ({ (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB m : 𝓞 K) }))
  · have hu := Ideal.span_singleton_eq_span_singleton.mp h
    refine ⟨hu.choose, fun w hw => Real.log_neg ?_ ?_⟩
    · simp only [pos_iff, ne_eq, ZeroMemClass.coe_eq_zero, ne_zero, not_false_eq_true]
    · calc
        _ = w ((_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB m : K) * (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB n : K)⁻¹) := by
          rw [← congr_arg ((↑) : (𝓞 K) → K) hu.choose_spec, mul_comm, Submonoid.coe_mul,
            ← mul_assoc, inv_mul_cancel (_root_.NumberField.Units.dirichletUnitTheorem.seq_ne_zero K w₁ hB n), one_mul]
        _ = w (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB m) * w (_root_.NumberField.Units.dirichletUnitTheorem.seq K w₁ hB n)⁻¹ := _root_.map_mul _ _ _
        _ < 1 := by
          rw [map_inv₀, mul_inv_lt_iff (pos_iff.mpr (_root_.NumberField.Units.dirichletUnitTheorem.seq_ne_zero K w₁ hB n)), mul_one]
          exact _root_.NumberField.Units.dirichletUnitTheorem.seq_decreasing K w₁ hB hnm w hw
  refine Set.Finite.exists_lt_map_eq_of_forall_mem
    (t := { I : Ideal (𝓞 K) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ B })
    (fun n => ?_) ?_
  · rw [Set.mem_setOf_eq, Ideal.absNorm_span_singleton]
    refine ⟨?_, _root_.NumberField.Units.dirichletUnitTheorem.seq_norm_le K w₁ hB n⟩
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (_root_.NumberField.Units.dirichletUnitTheorem.seq_norm_ne_zero K w₁ hB n))
  · rw [show { I : Ideal (𝓞 K) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ B } =
          (⋃ n ∈ Set.Icc 1 B, { I : Ideal (𝓞 K) | Ideal.absNorm I = n }) by ext; simp]
    exact Set.Finite.biUnion (Set.finite_Icc _ _) (fun n hn => Ideal.finite_setOf_absNorm_eq hn.1)

/-- Definition `NumberField.Units.dirichletUnitTheorem.exists_unit`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.exists_unit as "exists_unit"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}
variable (K)
open NumberField.mixedEmbedding
open NNReal
attribute [-instance] _root_.FractionalIdeal.commSemiring
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

theorem unitLattice_span_eq_top :
    Submodule.span ℝ (unitLattice K : Set ({w : InfinitePlace K // w ≠ w₀} → ℝ)) = ⊤ := by
  refine le_antisymm (le_top) ?_
  -- The standard basis
  let B := Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}
  -- The image by log_embedding of the family of units constructed above
  let v := fun w : { w : InfinitePlace K // w ≠ w₀ } => _root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K (_root_.NumberField.Units.dirichletUnitTheorem.exists_unit K w).choose
  -- To prove the result, it is enough to prove that the family `v` is linearly independent
  suffices B.det v ≠ 0 by
    rw [← isUnit_iff_ne_zero, ← is_basis_iff_det] at this
    rw [← this.2]
    exact Submodule.span_monotone (fun _ ⟨w, hw⟩ =>
      ⟨(_root_.NumberField.Units.dirichletUnitTheorem.exists_unit K w).choose, trivial, by rw [← hw]⟩)
  rw [Basis.det_apply]
  -- We use a specific lemma to prove that this determinant is nonzero
  refine det_ne_zero_of_sum_col_lt_diag (fun w => ?_)
  simp_rw [Real.norm_eq_abs, B, Basis.coePiBasisFun.toMatrix_eq_transpose, Matrix.transpose_apply]
  rw [← sub_pos, sum_congr rfl (fun x hx => abs_of_neg ?_), sum_neg_distrib, sub_neg_eq_add,
    sum_erase_eq_sub (mem_univ _), ← add_comm_sub]
  refine add_pos_of_nonneg_of_pos ?_ ?_
  · rw [sub_nonneg]
    exact le_abs_self _
  · rw [_root_.NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component (_root_.NumberField.Units.dirichletUnitTheorem.exists_unit K w).choose]
    refine mul_pos_of_neg_of_neg ?_ ((_root_.NumberField.Units.dirichletUnitTheorem.exists_unit K w).choose_spec _ w.prop.symm)
    rw [mult]; split_ifs <;> norm_num
  · refine mul_neg_of_pos_of_neg ?_ ((_root_.NumberField.Units.dirichletUnitTheorem.exists_unit K w).choose_spec x ?_)
    · rw [mult]; split_ifs <;> norm_num
    · exact Subtype.ext_iff_val.not.mp (ne_of_mem_erase hx)

/-- Definition `NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top as "unitLattice_span_eq_top"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice

def instZlattice_unitLattice : IsZlattice ℝ (_root_.NumberField.Units.unitLattice K) := {
  span_top := _root_.NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K
}

/-- Definition `NumberField.Units.instZlattice_unitLattice`. -/
DefinitionDoc NumberField.Units.instZlattice_unitLattice as "instZlattice_unitLattice"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}

theorem mult_log_place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} :
    mult w * Real.log (w x) = 0 ↔ w x = 1 := by
  rw [mul_eq_zero, or_iff_right, Real.log_eq_zero, or_iff_right, or_iff_left]
  · linarith [(apply_nonneg _ _ : 0 ≤ w x)]
  · simp only [ne_eq, map_eq_zero, _root_.NumberField.Units.coe_ne_zero x, not_false_eq_true]
  · refine (ne_of_gt ?_)
    rw [mult]; split_ifs <;> norm_num

/-- Definition `NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero as "mult_log_place_eq_zero"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators
open NumberField.InfinitePlace

namespace NumberField.Units.dirichletUnitTheorem

variable (K : Type*) [Field K]
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
open scoped Classical
open Finset
variable [NumberField K]
variable {K}
variable (K)
variable {K}

theorem logEmbedding_eq_zero_iff {x : (𝓞 K)ˣ} :
    _root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K x = 0 ↔ x ∈ _root_.NumberField.Units.torsion K := by
  rw [_root_.NumberField.Units.mem_torsion]
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · by_cases hw : w = _root_.NumberField.Units.dirichletUnitTheorem.w₀
    · suffices -mult _root_.NumberField.Units.dirichletUnitTheorem.w₀ * Real.log (_root_.NumberField.Units.dirichletUnitTheorem.w₀ (x : K)) = 0 by
        rw [neg_mul, neg_eq_zero, ← hw] at this
        exact _root_.NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero.mp this
      rw [← _root_.NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component, sum_eq_zero]
      exact fun w _ => congrFun h w
    · exact _root_.NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero.mp (congrFun h ⟨w, hw⟩)
  · ext w
    rw [_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding_component, h w.val, Real.log_one, mul_zero, Pi.zero_apply]

/-- Definition `NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff`. -/
DefinitionDoc NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff as "logEmbedding_eq_zero_iff"

end NumberField.Units.dirichletUnitTheorem

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice

def unitLatticeEquiv : (_root_.NumberField.Units.unitLattice K) ≃ₗ[ℤ] Additive ((𝓞 K)ˣ ⧸ (_root_.NumberField.Units.torsion K)) := by
  refine AddEquiv.toIntLinearEquiv ?_
  rw [_root_.NumberField.Units.unitLattice, ← AddMonoidHom.range_eq_map (_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K)]
  refine (QuotientAddGroup.quotientKerEquivRange (_root_.NumberField.Units.dirichletUnitTheorem.logEmbedding K)).symm.trans ?_
  refine (QuotientAddGroup.quotientAddEquivOfEq ?_).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (MonoidHom.toAdditive (QuotientGroup.mk' (_root_.NumberField.Units.torsion K))) (fun x => ?_))
  · ext
    rw [MonoidHom.coe_toAdditive_ker, QuotientGroup.ker_mk', AddMonoidHom.mem_ker,
      _root_.NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff]
    rfl
  · refine ⟨Additive.ofMul x.out', ?_⟩
    simp only [MonoidHom.toAdditive_apply_apply, toMul_ofMul, QuotientGroup.mk'_apply,
      QuotientGroup.out_eq']
    rfl

/-- Definition `NumberField.Units.unitLatticeEquiv`. -/
DefinitionDoc NumberField.Units.unitLatticeEquiv as "unitLatticeEquiv"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice

def _instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510 : Module.Free ℤ (Additive ((𝓞 K)ˣ ⧸ (_root_.NumberField.Units.torsion K))) := Module.Free.of_equiv (_root_.NumberField.Units.unitLatticeEquiv K)

/-- Definition `NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510`. -/
DefinitionDoc NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510 as "_instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510

def _instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513 : Module.Finite ℤ (Additive ((𝓞 K)ˣ ⧸ (_root_.NumberField.Units.torsion K))) := Module.Finite.equiv (_root_.NumberField.Units.unitLatticeEquiv K)

-- Note that we prove this instance first and then deduce from it the instance
-- `Monoid.FG (𝓞 K)ˣ`, and not the other way around, due to no `Subgroup` version
-- of `Submodule.fg_of_fg_map_of_fg_inf_ker` existing.

/-- Definition `NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513`. -/
DefinitionDoc NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513 as "_instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513

def _instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519 : Module.Finite ℤ (Additive (𝓞 K)ˣ) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (MonoidHom.toAdditive (QuotientGroup.mk' (_root_.NumberField.Units.torsion K))).toIntLinearMap ?_ ?_
  · rw [Submodule.map_top, LinearMap.range_eq_top.mpr
      (by exact QuotientGroup.mk'_surjective (_root_.NumberField.Units.torsion K)), ← Module.finite_def]
    infer_instance
  · rw [inf_of_le_right le_top, AddMonoidHom.coe_toIntLinearMap_ker, MonoidHom.coe_toAdditive_ker,
      QuotientGroup.ker_mk', Submodule.fg_iff_add_subgroup_fg,
      AddSubgroup.toIntSubmodule_toAddSubgroup, ← AddGroup.fg_iff_addSubgroup_fg]
    have : Finite (Subgroup.toAddSubgroup (_root_.NumberField.Units.torsion K)) := (inferInstance : Finite (_root_.NumberField.Units.torsion K))
    exact AddGroup.fg_of_finite

/-- Definition `NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519`. -/
DefinitionDoc NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519 as "_instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519

def _instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532 : Monoid.FG (𝓞 K)ˣ := by
  rw [Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
  infer_instance

/-- Definition `NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532`. -/
DefinitionDoc NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532 as "_instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532"

end NumberField.Units

end

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

noncomputable def _instance_m464c54332e4379636c6f_l177 : Fintype (𝓞 K ⧸ Ideal.span {λ}) := by
  refine Ideal.fintypeQuotientOfFreeOfNeBot _ (fun h ↦ ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero, ← Subtype.coe_inj] at h
  exact hζ.ne_one (by decide) h

/-- Definition `IsCyclotomicExtension.Rat.Three._instance_m464c54332e4379636c6f_l177`. -/
DefinitionDoc IsCyclotomicExtension.Rat.Three._instance_m464c54332e4379636c6f_l177 as "_instance_m464c54332e4379636c6f_l177"

end IsCyclotomicExtension.Rat.Three

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'

theorem zeta_sub_one_prime_of_two_pow [IsCyclotomicExtension {(2 : ℕ+) ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑((2 : ℕ+) ^ (k + 1))) :
    Prime (hζ.toInteger - 1) := by
  letI := IsCyclotomicExtension.numberField {(2 : ℕ+) ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt zero_lt_one (one_lt_pow (by decide) (by simp))
    rw [← Subalgebra.coe_eq_zero] at h
    simpa [sub_eq_zero] using h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  cases k
  · convert Prime.neg Int.prime_two
    apply RingHom.injective_int (algebraMap ℤ ℚ)
    rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), Subalgebra.algebraMap_eq]
    simp only [Nat.zero_eq, PNat.pow_coe, id.map_eq_id, RingHomCompTriple.comp_eq, RingHom.coe_coe,
      Subalgebra.coe_val, algebraMap_int_eq, map_neg, map_ofNat]
    simpa using hζ.pow_sub_one_norm_two (cyclotomic.irreducible_rat (by simp))
  convert Int.prime_two
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), Subalgebra.algebraMap_eq]
  simp only [PNat.pow_coe, id.map_eq_id, RingHomCompTriple.comp_eq, RingHom.coe_coe,
    Subalgebra.coe_val, algebraMap_int_eq, map_natCast]
  exact hζ.sub_one_norm_two Nat.AtLeastTwo.prop (cyclotomic.irreducible_rat (by simp))

/-- Definition `IsPrimitiveRoot.zeta_sub_one_prime_of_two_pow`. -/
DefinitionDoc IsPrimitiveRoot.zeta_sub_one_prime_of_two_pow as "zeta_sub_one_prime_of_two_pow"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'

theorem zeta_sub_one_prime_of_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (hζ.toInteger - 1) := by
  letI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt zero_lt_one (one_lt_pow hp.out.one_lt (by simp))
    rw [← Subalgebra.coe_eq_zero] at h
    simpa [sub_eq_zero] using h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  convert Nat.prime_iff_prime_int.1 hp.out
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), Subalgebra.algebraMap_eq]
  simp only [PNat.pow_coe, id.map_eq_id, RingHomCompTriple.comp_eq, RingHom.coe_coe,
    Subalgebra.coe_val, algebraMap_int_eq, map_natCast]
  exact hζ.sub_one_norm_prime_ne_two (Polynomial.cyclotomic.irreducible_rat (PNat.pos _)) hodd

/-- Definition `IsPrimitiveRoot.zeta_sub_one_prime_of_ne_two`. -/
DefinitionDoc IsPrimitiveRoot.zeta_sub_one_prime_of_ne_two as "zeta_sub_one_prime_of_ne_two"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'

theorem zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) : Prime (hζ.toInteger - 1) := by
  by_cases htwo : p = 2
  · subst htwo
    apply hζ.zeta_sub_one_prime_of_two_pow
  · apply hζ.zeta_sub_one_prime_of_ne_two htwo

/-- Definition `IsPrimitiveRoot.zeta_sub_one_prime`. -/
DefinitionDoc IsPrimitiveRoot.zeta_sub_one_prime as "zeta_sub_one_prime"

end IsPrimitiveRoot

end

section
open List

def FermatLastTheoremWith (α : Type*) [Semiring α] (n : ℕ) : Prop :=
  ∀ a b c : α, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n

/-- Definition `FermatLastTheoremWith`. -/
DefinitionDoc FermatLastTheoremWith as "FermatLastTheoremWith"

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional

def rank : ℕ := Fintype.card (InfinitePlace K) - 1

/-- Definition `NumberField.Units.rank`. -/
DefinitionDoc NumberField.Units.rank as "rank"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice

protected theorem finrank_eq_rank :
    finrank ℝ ({w : InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} → ℝ) = _root_.NumberField.Units.rank K := by
  simp only [finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_ofSubsingleton, _root_.NumberField.Units.rank]

/-- Definition `NumberField.Units.finrank_eq_rank`. -/
DefinitionDoc NumberField.Units.finrank_eq_rank as "finrank_eq_rank"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice

@[simp]
theorem unitLattice_rank :
    finrank ℤ (_root_.NumberField.Units.unitLattice K) = _root_.NumberField.Units.rank K := by
  rw [← _root_.NumberField.Units.finrank_eq_rank, Zlattice.rank ℝ]

/-- Definition `NumberField.Units.unitLattice_rank`. -/
DefinitionDoc NumberField.Units.unitLattice_rank as "unitLattice_rank"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532

theorem rank_modTorsion :
    FiniteDimensional.finrank ℤ (Additive ((𝓞 K)ˣ ⧸ (_root_.NumberField.Units.torsion K))) = _root_.NumberField.Units.rank K := by
  rw [← LinearEquiv.finrank_eq (_root_.NumberField.Units.unitLatticeEquiv K), _root_.NumberField.Units.unitLattice_rank]

/-- Definition `NumberField.Units.rank_modTorsion`. -/
DefinitionDoc NumberField.Units.rank_modTorsion as "rank_modTorsion"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532

def basisModTorsion : Basis (Fin (_root_.NumberField.Units.rank K)) ℤ (Additive ((𝓞 K)ˣ ⧸ (_root_.NumberField.Units.torsion K))) :=
  Basis.reindex (Module.Free.chooseBasis ℤ _) (Fintype.equivOfCardEq <| by
    rw [← FiniteDimensional.finrank_eq_card_chooseBasisIndex, _root_.NumberField.Units.rank_modTorsion, Fintype.card_fin])

/-- Definition `NumberField.Units.basisModTorsion`. -/
DefinitionDoc NumberField.Units.basisModTorsion as "basisModTorsion"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532

def fundSystem : Fin (_root_.NumberField.Units.rank K) → (𝓞 K)ˣ :=
  -- `:)` prevents the `⧸` decaying to a quotient by `leftRel` when we unfold this later
  fun i => Quotient.out' (Additive.toMul (_root_.NumberField.Units.basisModTorsion K i) :)

/-- Definition `NumberField.Units.fundSystem`. -/
DefinitionDoc NumberField.Units.fundSystem as "fundSystem"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532

theorem fun_eq_repr {x ζ : (𝓞 K)ˣ} {f : Fin (_root_.NumberField.Units.rank K) → ℤ} (hζ : ζ ∈ _root_.NumberField.Units.torsion K)
    (h : x = ζ * ∏ i, (_root_.NumberField.Units.fundSystem K i) ^ (f i)) :
    f = (_root_.NumberField.Units.basisModTorsion K).repr (Additive.ofMul ↑x) := by
  suffices Additive.ofMul ↑x = ∑ i, (f i) • (_root_.NumberField.Units.basisModTorsion K i) by
    rw [← (_root_.NumberField.Units.basisModTorsion K).repr_sum_self f, ← this]
  calc
    Additive.ofMul ↑x
    _ = ∑ i, (f i) • Additive.ofMul ↑(_root_.NumberField.Units.fundSystem K i) := by
          rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hζ, one_mul,
            QuotientGroup.mk_prod, ofMul_prod]; rfl
    _ = ∑ i, (f i) • (_root_.NumberField.Units.basisModTorsion K i) := by
          simp_rw [_root_.NumberField.Units.fundSystem, QuotientGroup.out_eq', ofMul_toMul]

/-- Definition `NumberField.Units.fun_eq_repr`. -/
DefinitionDoc NumberField.Units.fun_eq_repr as "fun_eq_repr"

end NumberField.Units

end

noncomputable section
open scoped NumberField
open NumberField
open Units
open BigOperators

namespace NumberField.Units

variable (K : Type*) [Field K]
open NumberField.InfinitePlace
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l115
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l118
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l129
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l132
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem
open FiniteDimensional
attribute [local instance] _root_.NumberField.Units.instDiscrete_unitLattice
attribute [local instance] _root_.NumberField.Units.instZlattice_unitLattice
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l510
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l513
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l519
attribute [local instance] _root_.NumberField.Units._instance_m464c54332e4d6174686c69622e4e756d6265725468656f72792e4e756d6265724669656c642e556e697473_l532

theorem exist_unique_eq_mul_prod (x : (𝓞 K)ˣ) : ∃! (ζ : _root_.NumberField.Units.torsion K) (e : Fin (_root_.NumberField.Units.rank K) → ℤ),
    x = ζ * ∏ i, (_root_.NumberField.Units.fundSystem K i) ^ (e i) := by
  let ζ := x * (∏ i, (_root_.NumberField.Units.fundSystem K i) ^ ((_root_.NumberField.Units.basisModTorsion K).repr (Additive.ofMul ↑x) i))⁻¹
  have h_tors : ζ ∈ _root_.NumberField.Units.torsion K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← ofMul_eq_zero,
      ofMul_mul, ofMul_inv, QuotientGroup.mk_prod, ofMul_prod]
    simp_rw [QuotientGroup.mk_zpow, ofMul_zpow, _root_.NumberField.Units.fundSystem, QuotientGroup.out_eq']
    rw [add_eq_zero_iff_eq_neg, neg_neg]
    exact ((_root_.NumberField.Units.basisModTorsion K).sum_repr (Additive.ofMul ↑x)).symm
  refine ⟨⟨ζ, h_tors⟩, ?_, ?_⟩
  · refine ⟨((_root_.NumberField.Units.basisModTorsion K).repr (Additive.ofMul ↑x) : Fin (_root_.NumberField.Units.rank K) → ℤ), ?_, ?_⟩
    · simp only [ζ, _root_.inv_mul_cancel_right]
    · exact fun _ hf => _root_.NumberField.Units.fun_eq_repr K h_tors hf
  · rintro η ⟨_, hf, _⟩
    simp_rw [_root_.NumberField.Units.fun_eq_repr K η.prop hf] at hf
    ext1; dsimp only [ζ]
    nth_rewrite 1 [hf]
    rw [_root_.mul_inv_cancel_right]

/-- Definition `NumberField.Units.exist_unique_eq_mul_prod`. -/
DefinitionDoc NumberField.Units.exist_unique_eq_mul_prod as "exist_unique_eq_mul_prod"

end NumberField.Units

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'

noncomputable def integralPowerBasis' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : PowerBasis ℤ (𝓞 K) :=
  @_root_.IsPrimitiveRoot.integralPowerBasis p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one])

/-- Definition `IsPrimitiveRoot.integralPowerBasis'`. -/
DefinitionDoc IsPrimitiveRoot.integralPowerBasis' as "integralPowerBasis'"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers

@[simp]
theorem integralPowerBasis_dim [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) : hζ.integralPowerBasis.dim = φ (p ^ k) := by
  simp [_root_.IsPrimitiveRoot.integralPowerBasis, ← cyclotomic_eq_minpoly hζ, natDegree_cyclotomic]

/-- Definition `IsPrimitiveRoot.integralPowerBasis_dim`. -/
DefinitionDoc IsPrimitiveRoot.integralPowerBasis_dim as "integralPowerBasis_dim"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'

@[simp]
theorem power_basis_int'_dim [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    hζ.integralPowerBasis'.dim = φ p := by
  erw [@_root_.IsPrimitiveRoot.integralPowerBasis_dim p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one]),
    pow_one]

/-- Definition `IsPrimitiveRoot.power_basis_int'_dim`. -/
DefinitionDoc IsPrimitiveRoot.power_basis_int'_dim as "power_basis_int'_dim"

end IsPrimitiveRoot

end

section
open Algebra
open IsCyclotomicExtension
open Polynomial
open NumberField
open scoped Cyclotomic
open scoped NumberField
open scoped Nat
open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]
attribute [local instance] _root_.IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers
attribute [local instance] _root_.IsCyclotomicExtension.ring_of_integers'

@[simp]
theorem integralPowerBasis'_gen [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    hζ.integralPowerBasis'.gen = hζ.toInteger :=
  @_root_.IsPrimitiveRoot.integralPowerBasis_gen p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one])

/-- Definition `IsPrimitiveRoot.integralPowerBasis'_gen`. -/
DefinitionDoc IsPrimitiveRoot.integralPowerBasis'_gen as "integralPowerBasis'_gen"

end IsPrimitiveRoot

end

section
open List

def FermatLastTheoremFor (n : ℕ) : Prop := _root_.FermatLastTheoremWith ℕ n

/-- Definition `FermatLastTheoremFor`. -/
DefinitionDoc FermatLastTheoremFor as "FermatLastTheoremFor"

end
