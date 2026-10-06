import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.TFAE
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RootsOfUnity.Basic
import Game.Levels.FermatSLastTheoremForExponent3.L52_final
import Game.Generated.DefsAfter015
import Game.Generated.DefsAfter033
import Game.Generated.DefsAfter063
import Game.Generated.DefsAfter064
import Game.Generated.DefsAfter065
import Game.Generated.DefsAfter072
import Game.Generated.DefsAfter073
import GameServer.Commands

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

noncomputable
def _root_.Solution'_final : _root_.Solution' where
  a := S.Y
  b := S.u₄ * S.Z
  c := λ ^ (S.multiplicity - 1) * S.X
  u := S.u₅
  ha := S.lambda_not_dvd_Y
  hb := fun h ↦ S.lambda_not_dvd_Z <| Units.dvd_mul_left.1 h
  hc := fun h ↦ S.X_ne_zero <| by simpa [_root_.IsCyclotomicExtension.Rat.Three.lambda_ne_zero] using h
  coprime := (isCoprime_mul_unit_left_right S.u₄.isUnit _ _).2 S.coprime_Y_Z
  hcdvd := by
    refine dvd_mul_of_dvd_left (dvd_pow_self _ (fun h ↦ ?_)) _
    rw [Nat.sub_eq_iff_eq_add (le_trans (by norm_num) S.two_le_multiplicity), zero_add] at h
    simpa [h] using S.two_le_multiplicity
  H := _root_.Solution.final S

/-- Let $K = \Q(\zeta_3)$ be the third cyclotomic field. \\
Let $\cc{O}_K = \Z[\zeta_3]$ be the ring of integers of $K$. \\
Let $\cc{O}^\times_K$ be the group of units of $\cc{O}_K$. \\
Let $\zeta_3 \in K$ be any primitive third root of unity. \\
Let $\eta \in \cc{O}_K$ be the element corresponding to $\zeta_3 \in K$. \\
Let $\lambda \in \cc{O}_K$ be such that $\lambda = \eta -1$. \\
Let $S = (a,b,c,u)$ be a $solution$ with multiplicity $n$.\\
Let $S_f' = (Y,u_4 Z, \lambda^{n-1} X, u_5)$.\\\\
Then $S_f'$ is a $solution'$. -/
DefinitionDoc Solution'_final as "Solution'_final"

end Solution

end
