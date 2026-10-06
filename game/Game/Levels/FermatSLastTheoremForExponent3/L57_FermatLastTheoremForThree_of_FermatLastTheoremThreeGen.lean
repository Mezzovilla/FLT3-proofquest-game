import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L56_fermatLastTheoremForThreeGen

World "FermatSLastTheoremForExponent3"
Level 57

Title "FermatLastTheoremForThree_of_FermatLastTheoremThreeGen"

Introduction "
To prove *Fermat's Last Theorem for Exponent $3$*,
it suffices to prove *Generalised Fermat's Last Theorem for Exponent $3$*. \\\\
Equivalently, *Generalised Fermat's Last Theorem for Exponent $3$* implies
*Fermat's Last Theorem for Exponent $3$*.
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

/-- To prove *Fermat's Last Theorem for Exponent $3$*,
it suffices to prove *Generalised Fermat's Last Theorem for Exponent $3$*. \\
Equivalently, *Generalised Fermat's Last Theorem for Exponent $3$* implies
*Fermat's Last Theorem for Exponent $3$*. -/
TheoremDoc FermatLastTheoremForThree_of_FermatLastTheoremThreeGen as "FermatLastTheoremForThree_of_FermatLastTheoremThreeGen" in "Fermat's Last Theorem for Exponent 3"

Statement FermatLastTheoremForThree_of_FermatLastTheoremThreeGen :
    _root_.FermatLastTheoremForThreeGen → _root_.FermatLastTheoremFor 3 := by
  Hint "Assume that $\\forall a, b, c \\in \\cc\u007bO\u007d_K,\\, \\forall u \\in \\cc\u007bO\u007d^\\times_K$ such that $c \\neq 0$,
$\\gcd(a,b)=1$, $\\lambda \\notdivides a$, $\\lambda \\notdivides b$ and $\\lambda \\divides c$,
it holds that $a^3 + b^3 \\neq u c^3$.
Let $a, b, c \\in \\Z$ such that $a\\neq 0$, $b\\neq 0$ and $c\\neq 0$.
By *thm:fermatLastTheoremThree_of_three_dvd_only_c*, we can assume that
$\\gcd(a,b)=1$, $3 \\notdivides a$, $3 \\notdivides b$, $3 \\divides c$.
By contradiction we assume that $a^3 + b^3 = c^3$ and let $u = 1$.
\\begin\u007bitemize\u007d
\\item By contradiction we assume that $\\lambda \\divides a$, which implies that the norm of
$\\lambda$ divides $a$ by *lmm:norm_lambda_prime*, which implies that $3 \\divides a$ by
*lmm:norm_lambda*, that contradicts the assumption that $3 \\notdivides a$ forcing us
to conclude that $\\lambda \\notdivides a$.
\\item By contradiction we assume that $\\lambda \\divides b$, which implies that the norm of
$\\lambda$ divides $b$ by *lmm:norm_lambda_prime*, which implies that $3 \\divides b$ by
*lmm:norm_lambda*, that contradicts the assumption that $3 \\notdivides b$ forcing us
to conclude that $\\lambda \\notdivides b$.
\\item $\\lambda \\divides 3$ by *lmm:lambda_dvd_three* and $3 \\divides c$,
then $\\lambda \\divides c$.
\\end\u007bitemize\u007d
By our first assumption $a^3 + b^3 \\neq u c^3 = 1 c^3 = c^3 = a^3 + b^3$ which is absurd."
  intro H
  refine _root_.fermatLastTheoremThree_of_three_dvd_only_c (fun a b c hc ha hb ⟨x, hx⟩ hcoprime h ↦ ?_)
  refine H a b c 1 (by simp [hc]) (fun hdvd ↦ ha ?_) (fun hdvd ↦ hb ?_) ?_ ?_ ?_
  · rwa [← Ideal.norm_dvd_iff (_root_.IsCyclotomicExtension.Rat.Three.norm_lambda_prime _root_.hζ), _root_.IsCyclotomicExtension.Rat.Three.norm_lambda _root_.hζ] at hdvd
  · rwa [← Ideal.norm_dvd_iff (_root_.IsCyclotomicExtension.Rat.Three.norm_lambda_prime _root_.hζ), _root_.IsCyclotomicExtension.Rat.Three.norm_lambda _root_.hζ] at hdvd
  · exact dvd_trans (_root_.IsCyclotomicExtension.Rat.Three.lambda_dvd_three _root_.hζ) ⟨x, by simp [hx]⟩
  · rw [show a = algebraMap _ (𝓞 K) a by simp, show b = algebraMap _ (𝓞 K) b by simp]
    exact hcoprime.map _
  · simp only [Units.val_one, one_mul]
    exact_mod_cast h

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
