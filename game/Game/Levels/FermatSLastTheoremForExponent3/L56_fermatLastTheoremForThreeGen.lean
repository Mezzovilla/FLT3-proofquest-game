import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L55_exists_Solution_multiplicity_lt

World "FermatSLastTheoremForExponent3"
Level 56

Title "Generalised Fermat's Last Theorem for Exponent $3$"

Introduction "
Let $K = \\Q(\\zeta_3)$ be the third cyclotomic field. \\\\
Let $\\cc{O}_K = \\Z[\\zeta_3]$ be the ring of integers of $K$. \\\\
Let $\\cc{O}^\\times_K$ be the group of units of $\\cc{O}_K$. \\\\
Let $\\zeta_3 \\in K$ be any primitive third root of unity. \\\\
Let $\\eta \\in \\cc{O}_K$ be the element corresponding to $\\zeta_3 \\in K$. \\\\
Let $\\lambda \\in \\cc{O}_K$ be such that $\\lambda = \\eta -1$. \\\\
Let $a, b, c \\in \\cc{O}_K$ and $u \\in \\cc{O}^\\times_K$ such that $c \\neq 0$ and $\\gcd(a,b)=1$.\\\\
Let $\\lambda \\notdivides a$, $\\lambda \\notdivides b$ and $\\lambda \\divides c$. \\\\\\\\
Then $a^3 + b^3 \\neq u c^3$.
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

/-- Let $K = \Q(\zeta_3)$ be the third cyclotomic field. \\
Let $\cc{O}_K = \Z[\zeta_3]$ be the ring of integers of $K$. \\
Let $\cc{O}^\times_K$ be the group of units of $\cc{O}_K$. \\
Let $\zeta_3 \in K$ be any primitive third root of unity. \\
Let $\eta \in \cc{O}_K$ be the element corresponding to $\zeta_3 \in K$. \\
Let $\lambda \in \cc{O}_K$ be such that $\lambda = \eta -1$. \\
Let $a, b, c \in \cc{O}_K$ and $u \in \cc{O}^\times_K$ such that $c \neq 0$ and $\gcd(a,b)=1$.\\
Let $\lambda \notdivides a$, $\lambda \notdivides b$ and $\lambda \divides c$. \\\\
Then $a^3 + b^3 \neq u c^3$. -/
TheoremDoc fermatLastTheoremForThreeGen as "fermatLastTheoremForThreeGen" in "Fermat's Last Theorem for Exponent 3"

Statement fermatLastTheoremForThreeGen : _root_.FermatLastTheoremForThreeGen := by
  Hint "By contradiction we assume that there are $a, b, c \\in \\cc\u007bO\u007d_K$ and $u \\in \\cc\u007bO\u007d^\\times_K$
such that $c \\neq 0$, $\\gcd(a,b)=1$, $\\lambda \\notdivides a$, $\\lambda \\notdivides b$,
$\\lambda \\divides c$ and $a^3 + b^3 = u c^3$.
Then $S'=(a,b,c,u)$ is a $solution'$, which implies that there is a $solution$ $S$ by
*lmm:exists_Solution_of_Solution1*.
Then, by *lmm:exists_minimal*, there is a minimal solution $S_0$ with multiplicity $n$.
Hence, there is a $solution'$ $S_1'$ with multiplicity $m<n$ by *lmm:exists_Solution_multiplicity_lt*,
which implies that there is a $solution$ $S_1$  with multiplicity $m$ by *lmm:exists_Solution_of_Solution1*.
However, this contradicts the minimality of $S_0$
forcing us to conclude that $a^3 + b^3 \\neq u c^3$."
  intro a b c u hc ha hb hcdvd coprime H
  let S' : _root_.Solution' :=
  { a := a
    b := b
    c := c
    u := u
    ha := ha
    hb := hb
    hc := hc
    coprime := coprime
    hcdvd := hcdvd
    H := H }
  obtain ⟨S, -⟩ := _root_.exists_Solution_of_Solution' S'
  obtain ⟨Smin, hSmin⟩ := S.exists_minimal
  obtain ⟨Sfin, hSfin⟩ := Smin.exists_Solution_multiplicity_lt
  linarith [hSmin Sfin]

NewDefinition FermatLastTheoremForThreeGen
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
