import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L08_Solution_exists_minimal

World "FermatSLastTheoremForExponent3"
Level 9

Title "a_cube_b_cube_same_congr"

Introduction "
Let $S'=(a, b, c, u)$ be a $solution'$. \\\\\\\\
Then $\\lambda^4 \\divides a^3 - 1 \\land \\lambda^4 \\divides b^3 + 1$ or
$\\lambda^4 \\divides a^3 + 1 \\land \\lambda^4 \\divides b^3 - 1$.
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
Then $\lambda^4 \divides a^3 - 1 \land \lambda^4 \divides b^3 + 1$ or
$\lambda^4 \divides a^3 + 1 \land \lambda^4 \divides b^3 - 1$. -/
TheoremDoc a_cube_b_cube_same_congr as "a_cube_b_cube_same_congr" in "Fermat's Last Theorem for Exponent 3"

Statement a_cube_b_cube_same_congr :
    λ ^ 4 ∣ S.a ^ 3 - 1 ∧ λ ^ 4 ∣ S.b ^ 3 + 1 ∨  λ ^ 4 ∣ S.a ^ 3 + 1 ∧ λ ^ 4 ∣ S.b ^ 3 - 1 := by
  Hint "Since $\\lambda \\notdivides a$, then
$\\lambda^4 \\divides a^3 - 1 \\lor \\lambda^4 \\divides a^3 + 1$ by
*lmm:lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd*.
Since $\\lambda \\notdivides b$, then
$\\lambda^4 \\divides b^3 - 1 \\lor \\lambda^4 \\divides b^3 + 1$ by
*lmm:lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd*.
We proceed by analysing each case:
\\begin\u007bitemize\u007d
\\item Case $\\lambda^4 \\divides a^3 - 1 \\land \\lambda^4 \\divides b^3 - 1$.
Since $\\lambda \\divides c$ we have that $\\lambda \\divides c^3-(a^3-1)-(b^3-1) = 2$,
which is absurd by *lmm:lambda_not_dvd_two*.
\\item Case $\\lambda^4 \\divides a^3 + 1 \\land \\lambda^4 \\divides b^3 + 1$.
Since $\\lambda \\divides c$ we have that $\\lambda \\divides (a^3-1)+(b^3-1)-c^3 = 2$,
which is absurd by *lmm:lambda_not_dvd_two*.
\\item Case $\\lambda^4 \\divides a^3 - 1 \\land \\lambda^4 \\divides b^3 + 1$. Trivial.
\\item Case $\\lambda^4 \\divides a^3 + 1 \\land \\lambda^4 \\divides b^3 - 1$. Trivial.
\\end\u007bitemize\u007d"
  obtain ⟨z, hz⟩ := S.hcdvd
  rcases _root_.IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd _root_.hζ S.ha with
    (⟨x, hx⟩ | ⟨x, hx⟩) <;>
  rcases _root_.IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd _root_.hζ S.hb with
    (⟨y, hy⟩ | ⟨y, hy⟩)
  · exfalso
    refine _root_.IsCyclotomicExtension.Rat.Three.lambda_not_dvd_two _root_.hζ ⟨S.u * λ ^ 2 * z ^ 3 - λ ^ 3 * (x + y), ?_⟩
    symm
    calc _ = S.u * (λ * z) ^ 3 - λ ^ 4 * x - λ ^ 4 * y := by ring
    _ = (S.a ^ 3 + S.b ^ 3) - (S.a ^ 3 - 1) - (S.b ^ 3 - 1) := by rw [← hx, ← hy, ← hz, ← S.H]
    _ = 2 := by ring
  · left
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · right
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · exfalso
    refine _root_.IsCyclotomicExtension.Rat.Three.lambda_not_dvd_two _root_.hζ ⟨λ ^ 3 * (x + y) - S.u * λ ^ 2 * z ^ 3, ?_⟩
    symm
    calc _ =  λ ^ 4 * x + λ ^ 4 * y - S.u * (λ * z) ^ 3 := by ring
    _ = (S.a ^ 3 + 1) + (S.b ^ 3 + 1) - (S.a ^ 3 + S.b ^ 3) := by rw [← hx, ← hy, ← hz, ← S.H]
    _ = 2 := by ring

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
