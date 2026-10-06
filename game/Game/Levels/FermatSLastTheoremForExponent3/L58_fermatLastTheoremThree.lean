import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L57_FermatLastTheoremForThree_of_FermatLastTheoremThreeGen

World "FermatSLastTheoremForExponent3"
Level 58

Title "Fermat's Last Theorem for Exponent $3$"

Introduction "
Let $a, b, c \\in \\N$. \\\\
Let $a \\neq 0$, $b \\neq 0$ and $c \\neq 0$. \\\\\\\\
Then $a^3 + b^3 \\neq c^3$.
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
attribute [local instance] _root_.IsCyclotomicExtension.Rat.three_pid
attribute [local instance] _root_._instance_m464c54332e464c5433_l154
attribute [local instance] _root_._instance_m464c54332e464c5433_l163

/-- Let $a, b, c \in \N$. \\
Let $a \neq 0$, $b \neq 0$ and $c \neq 0$. \\\\
Then $a^3 + b^3 \neq c^3$. -/
TheoremDoc fermatLastTheoremThree as "fermatLastTheoremThree" in "Fermat's Last Theorem for Exponent 3"

Statement fermatLastTheoremThree : _root_.FermatLastTheoremFor 3 := by
  Hint "By *lmm:FermatLastTheoremForThree_of_FermatLastTheoremThreeGen*
and *Generalised Fermat's Last Theorem for Exponent $3$*, we can conclude that
$$a^3 + b^3 \\neq c^3.$$"
  apply _root_.FermatLastTheoremForThree_of_FermatLastTheoremThreeGen
  exact _root_.fermatLastTheoremForThreeGen
  --#print axioms fermatLastTheoremThree

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
