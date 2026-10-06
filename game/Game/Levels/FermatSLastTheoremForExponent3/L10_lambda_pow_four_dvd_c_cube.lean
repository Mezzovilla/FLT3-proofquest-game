import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L09_a_cube_b_cube_same_congr

World "FermatSLastTheoremForExponent3"
Level 10

Title "lambda_pow_four_dvd_c_cube"

Introduction "
Let $S'=(a, b, c, u)$ be a $solution'$. \\\\\\\\
Then $\\lambda^4 \\divides c^3$.
"

namespace NumberField
end NumberField

namespace IsCyclotomicExtension.Rat.Three
end IsCyclotomicExtension.Rat.Three

section
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
open NumberField
open nonZeroDivisors
open IsCyclotomicExtension.Rat.Three
open scoped Classical
attribute [local instance] _root_.IsCyclotomicExtension.Rat.three_pid
local notation "K" => CyclotomicField 3 ℚ
attribute [local instance] _root_._instance_m464c54332e464c5433_l154
attribute [-instance] _root_.ValuationRing.instIsBezoutToRing
attribute [local instance] _root_._instance_m464c54332e464c5433_l161
attribute [local instance] _root_._instance_m464c54332e464c5433_l163
local notation "η" => _root_.hζ.toInteger
local notation "λ" => η - 1
variable (S : _root_.Solution')

/-- Let $S'=(a, b, c, u)$ be a $solution'$. \\\\
Then $\lambda^4 \divides c^3$. -/
TheoremDoc lambda_pow_four_dvd_c_cube as "lambda_pow_four_dvd_c_cube" in "Fermat's Last Theorem for Exponent 3"

Statement lambda_pow_four_dvd_c_cube : λ ^ 4 ∣ S.c ^ 3 := by
  Hint "Apply *lmm:a_cube_b_cube_same_congr* and then compute each case."
  rcases _root_.a_cube_b_cube_same_congr S with
    (⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩) <;> {
  refine ⟨S.u⁻¹ * (x + y), ?_⟩
  symm
  calc _ = S.u⁻¹ * (λ ^ 4 * x + λ ^ 4 * y) := by ring
  _ = S.u⁻¹ * (S.a ^ 3 + S.b ^ 3) := by rw [← hx, ← hy]; ring
  _ = S.u⁻¹ * (S.u * S.c ^ 3) := by rw [S.H]
  _ = S.c ^ 3 := by simp }

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
