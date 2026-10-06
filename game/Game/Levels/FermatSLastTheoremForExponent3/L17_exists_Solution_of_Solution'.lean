import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L16_ex_dvd_a_add_b

World "FermatSLastTheoremForExponent3"
Level 17

Title "exists_Solution_of_Solution'"

Introduction "
Let $S'$ be a $solution'$ with multiplicity $n$.\\\\\\\\
Then there is a $solution\\text{ }S$ with multiplicity $n$.
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

/-- Let $S'$ be a $solution'$ with multiplicity $n$.\\\\
Then there is a $solution\text{ }S$ with multiplicity $n$. -/
TheoremDoc exists_Solution_of_Solution' as "exists_Solution_of_Solution'" in "Fermat's Last Theorem for Exponent 3"

Statement exists_Solution_of_Solution' : ∃ (S₁ : _root_.Solution), S₁.multiplicity = S.multiplicity := by
  Hint "Let $S'=(a',b',c',u')$. Let $a, b$ be the units given by *lmm:ex_dvd_a_add_b*.
Then $S=(a,b,c',u')$ is a $solution'$ with multiplicity $n$."
  obtain ⟨a, b, H, coprime, ha, hb, hab⟩ := _root_.ex_dvd_a_add_b S
  exact ⟨
  { a := a
    b := b
    c := S.c
    u := S.u
    ha := ha
    hb := hb
    hc := S.hc
    coprime := coprime
    hcdvd := S.hcdvd
    H := H
    hab := hab }, rfl⟩

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
