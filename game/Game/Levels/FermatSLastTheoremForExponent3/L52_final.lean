import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L51_by_kummer

World "FermatSLastTheoremForExponent3"
Level 52

Title "final"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $S$ be a $solution$ with multiplicity $n$.\\\\\\\\
Then $Y^3 + (u_4 Z)^3 = u_5 (\\lambda^{n-1} X)^3$.
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

/-- Let $K = \Q(\zeta_3)$ be the third cyclotomic field. \\
Let $\cc{O}_K = \Z[\zeta_3]$ be the ring of integers of $K$. \\
Let $\cc{O}^\times_K$ be the group of units of $\cc{O}_K$. \\
Let $\zeta_3 \in K$ be any primitive third root of unity. \\
Let $\eta \in \cc{O}_K$ be the element corresponding to $\zeta_3 \in K$. \\
Let $\lambda \in \cc{O}_K$ be such that $\lambda = \eta -1$. \\
Let $S$ be a $solution$ with multiplicity $n$.\\\\
Then $Y^3 + (u_4 Z)^3 = u_5 (\lambda^{n-1} X)^3$. -/
TheoremDoc Solution.final as "final" in "Fermat's Last Theorem for Exponent 3"

Statement final : S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3 := by
  Hint "By *lmm:by_kummer*, we have that $u_4 \\in \\set\u007b-1,1\u007d$, which implies that $u_4^2 = 1$.\\\\
Therefore, by *lmm:formula2*, we can conclude that
$$Y^3 + (u_4 Z)^3 = u_5 (\\lambda^\u007bn-1\u007d X)^3.$$"
  rw [show S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.Y ^ 3 + S.u₄^2 * S.u₄ * S.Z ^ 3 by ring]
  have f2 := _root_.Solution.formula2 S
  rw [show _root_.Solution.Y S ^ 3 + ↑(_root_.Solution.u₄ S) * _root_.Solution.Z S ^ 3 = _root_.Solution.Y S ^ 3 + 1 * ↑(_root_.Solution.u₄ S) * _root_.Solution.Z S ^ 3 by ring] at f2
  have simple_kummer := _root_.Solution.by_kummer S
  simp only [Finset.mem_insert, Finset.mem_singleton] at simple_kummer
  have hh : S.u₄ ^ 2 = (1 : 𝓞 K) := by
    rcases simple_kummer with (h | h) <;> simp only [h, one_pow, even_two, Even.neg_pow, one_pow]
  nth_rewrite 1 [← hh] at f2
  exact f2

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end Solution

end

Conclusion "Level completed! 🎉"
