import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L46_u₄'_isUnit
import Game.Generated.DefsAfter072

World "FermatSLastTheoremForExponent3"
Level 47

Title "u₅'_isUnit"

Introduction "
Let $S$ be a $solution$.\\\\\\\\
Then $u_5'$ is a unit.
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
Then $u_5'$ is a unit. -/
TheoremDoc Solution.u₅'_isUnit as "u₅'_isUnit" in "Fermat's Last Theorem for Exponent 3"

Statement u₅'_isUnit : IsUnit S.u₅' := by
  Hint "By *$u_4',u_5'$* $u_5' = -\\eta^2 u_1 u_2^\u007b-1\u007d$,
which is a product of units since $\\eta^3 = 1$ by *lmm:toInteger_cube_eq_one* and
$-\\eta (-\\eta^2) = \\eta^3$.
Since the product of units is a unit (multiplicative closure),
it follows that $u_5'$ must also be a unit."
  unfold _root_.Solution.u₅'
  rw [IsUnit.mul_iff, IsUnit.mul_iff]
  have minus_eta_sq_is_unit : IsUnit (- η ^ 2) := by
    apply isUnit_iff_exists_inv.2
    use (-η)
    ring_nf
    exact _root_.hζ.toInteger_cube_eq_one
  constructor
  · constructor
    · exact minus_eta_sq_is_unit
    · simp only [Units.isUnit]
  · simp only [Units.isUnit]

NewTactic ring_nf constructor
NewTheorem isUnit_iff_exists_inv
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
