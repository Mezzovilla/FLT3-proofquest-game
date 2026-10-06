import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L50_lambda_sq_div_new_X_cubed

World "FermatSLastTheoremForExponent3"
Level 51

Title "by_kummer"

Introduction "
Let $S$ be a $solution$.\\\\\\\\
Then $u_4 \\in \\set{-1,1} \\subset \\cc{O}_K$.
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

/-- Let $S$ be a $solution$.\\\\
Then $u_4 \in \set{-1,1} \subset \cc{O}_K$. -/
TheoremDoc Solution.by_kummer as "by_kummer" in "Fermat's Last Theorem for Exponent 3"

Statement by_kummer : ↑S.u₄ ∈ ({1, -1} : Finset (𝓞 K)) := by
  Hint "Let $n \\in \\N$ be the multiplicity of the solution $S$.\\\\
By *lmm:eq_one_or_neg_one_of_unit_of_congruent*, it suffices to prove that
$$\\exists m \\in \\Z \\text\u007b such that \u007d \\lambda^2 \\divides u_4 - m.$$
By *lmm:lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd*
and *lmm:lambda_not_dvd_Y*, we have that
$$(\\lambda^4 \\divides Y^3 - 1) \\lor (\\lambda^4 \\divides Y^3 + 1).$$
By *lmm:lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd*
and *lmm:lambda_not_dvd_Z*, we have that
$$(\\lambda^4 \\divides Z^3 - 1) \\lor (\\lambda^4 \\divides Z^3 + 1).$$
We proceed by analysing each case:
\\begin\u007bitemize\u007d
\\item Case $(\\lambda^4 \\divides Y^3 - 1) \\land (\\lambda^4 \\divides Z^3 - 1)$. \\\\
Let $m=-1$ and consider the fact that
$$u_4 - m = Y^3 + u_4 Z^3 - (Y^3 - 1) - u_4 (Z^3 - 1).$$
By *lmm:formula2*, we have that
$$u_4 - m = u_5 (\\lambda^\u007bn-1\u007d X)^3 - (Y^3 - 1) - u_4 (Z^3 - 1).$$
Since, by *lmm:lambda_sq_div_new_X_cubed*, we know that
$$\\lambda^2 \\divides u_5 (\\lambda^\u007bn-1\u007d X)^3$$
and, by *lmm:lambda_sq_div_lambda_fourth* and by assumption, we have that
$$\\lambda^2 \\divides Y^3 - 1 \\land \\lambda^2 \\divides Z^3 - 1,$$
Then, we can conclude that
$$\\lambda^2 \\divides u_4 - m.$$
\\item Case $(\\lambda^4 \\divides Y^3 - 1) \\land (\\lambda^4 \\divides Z^3 + 1)$. \\\\
Let $m=1$ and proceed similarly to the first case.
\\item Case $(\\lambda^4 \\divides Y^3 + 1) \\land (\\lambda^4 \\divides Z^3 - 1)$. \\\\
Let $m=1$ and proceed similarly to the first case.
\\item Case $(\\lambda^4 \\divides Y^3 + 1) \\land (\\lambda^4 \\divides Z^3 + 1)$. \\\\
Let $m=-1$ and proceed similarly to the first case.
\\end\u007bitemize\u007d"
  have h0 := _root_.Solution.lambda_sq_div_lambda_fourth
  have hX := _root_.Solution.lambda_sq_div_new_X_cubed S
  suffices hh : S.u₄ = 1 ∨ S.u₄ = -1 by
    rcases hh with (h | h) <;> simp [h]
  apply _root_.IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent _root_.hζ
  rcases hX with ⟨kX, hkX⟩
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd _root_.hζ S.lambda_not_dvd_Y with
    (HY | HY) <;> rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd
      _root_.hζ S.lambda_not_dvd_Z with (HZ | HZ) <;> replace HY := h0.trans HY <;> replace HZ :=
      h0.trans HZ <;> rcases HY with ⟨kY, hkY⟩ <;> rcases HZ with ⟨kZ, hkZ⟩
  · use -1
    use kX - kY - S.u₄ * kZ
    rw [show λ ^ 2 * (kX - kY - ↑(_root_.Solution.u₄ S) * kZ) = λ ^ 2 * kX - λ ^ 2 * kY - ↑(_root_.Solution.u₄ S) * (λ ^ 2 * kZ) by ring]
    rw [← hkX, ← hkY, ← hkZ, ← S.formula2]
    ring
  · use 1
    use - kX + kY + S.u₄ * kZ
    rw [show λ ^ 2 * (-kX + kY + ↑(_root_.Solution.u₄ S) * kZ) = - (λ ^ 2 * kX - λ ^ 2 * kY - ↑(_root_.Solution.u₄ S) * (λ ^ 2 * kZ)) by ring]
    rw [← hkX, ← hkY, ← hkZ, ← S.formula2]
    ring
  · use 1
    use kX - kY - S.u₄ * kZ
    rw [show λ ^ 2 * (kX - kY - ↑(_root_.Solution.u₄ S) * kZ) = λ ^ 2 * kX - λ ^ 2 * kY - ↑(_root_.Solution.u₄ S) * (λ ^ 2 * kZ) by ring]
    rw [← hkX, ← hkY, ← hkZ, ← S.formula2]
    ring
  · use -1
    use - kX + kY + S.u₄ * kZ
    rw [show λ ^ 2 * (-kX + kY + ↑(_root_.Solution.u₄ S) * kZ) = - (λ ^ 2 * kX - λ ^ 2 * kY - ↑(_root_.Solution.u₄ S) * (λ ^ 2 * kZ)) by ring]
    rw [← hkX, ← hkY, ← hkZ, ← S.formula2]
    ring

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
