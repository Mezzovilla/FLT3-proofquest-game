import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L52_final
import Game.Generated.DefsAfter078

World "FermatSLastTheoremForExponent3"
Level 53

Title "Solution'_final_multiplicity"

Introduction "
Let $S$ be a $solution$ with multiplicity $n$.\\\\\\\\
Then $S_f'$ has multiplicity $n-1$.
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

open Solution
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

/-- Let $S$ be a $solution$ with multiplicity $n$.\\\\
Then $S_f'$ has multiplicity $n-1$. -/
TheoremDoc Solution'_final_multiplicity as "Solution'_final_multiplicity" in "Fermat's Last Theorem for Exponent 3"

Statement Solution'_final_multiplicity :
    (_root_.Solution'_final S).multiplicity = S.multiplicity - 1 := by
  Hint "Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc\u007bO\u007d_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc\u007bO\u007d^\\times_K$ be the group of units of $\\cc\u007bO\u007d_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc\u007bO\u007d_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc\u007bO\u007d_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $(a',b',c',u') = S_f'$ be the final $solution'$, then
$\\lambda^\u007bn-1\u007d \\divides \\lambda^\u007bn-1\u007d X = c'$.
By contradiction we assume that $\\lambda^n \\divides c'$ which implies that $\\lambda \\divides X$,
that contradicts *lmm:lambda_not_dvd_X* forcing us to conclude
that $\\lambda^\u007bn\u007d \\notdivides c'$. Then $S_f'$ has multiplicity $n-1$."
  refine (multiplicity.unique' (by simp [_root_.Solution'_final]) (fun h ↦ S.lambda_not_dvd_X ?_)).symm
  obtain ⟨k, hk : λ ^ (S.multiplicity - 1) * S.X = λ ^ (S.multiplicity - 1 + 1) * k⟩ := h
  rw [pow_succ, mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', _root_.IsCyclotomicExtension.Rat.Three.lambda_ne_zero, ne_eq, false_and,
    or_false] at hk
  simp [hk]

NewDefinition Solution'_final
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
