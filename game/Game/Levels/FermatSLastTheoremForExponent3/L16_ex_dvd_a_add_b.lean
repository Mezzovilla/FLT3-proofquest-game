import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L15_lambda_sq_dvd_or_dvd_or_dvd

World "FermatSLastTheoremForExponent3"
Level 16

Title "ex_dvd_a_add_b"

Introduction "
Let $S'=(a, b, c, u)$ be a $solution'$.\\\\\\\\
Then $\\exists a_1,b_1 \\in \\cc{O}_k$ such that $S_1=(a_1,b_1,c,u)$ is a $solution$.
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

/-- Let $S'=(a, b, c, u)$ be a $solution'$.\\\\
Then $\exists a_1,b_1 \in \cc{O}_k$ such that $S_1=(a_1,b_1,c,u)$ is a $solution$. -/
TheoremDoc ex_dvd_a_add_b as "ex_dvd_a_add_b" in "Fermat's Last Theorem for Exponent 3"

Statement ex_dvd_a_add_b : ∃ (a' b' : 𝓞 K), a' ^ 3 + b' ^ 3 = S.u * S.c ^ 3 ∧
    IsCoprime a' b' ∧ ¬ λ ∣ a' ∧ ¬ λ ∣ b' ∧ λ ^ 2 ∣ a' + b' := by
  Hint "By *lmm:lambda_sq_dvd_or_dvd_or_dvd*, we have that
$$(\\lambda^2 \\divides a + b) \\lor (\\lambda^2 \\divides a +
\\eta b) \\lor (\\lambda^2 \\divides a + \\eta^2 b).$$
We proceed by analysing each case:
\\begin\u007bitemize\u007d
\\item Case $\\lambda^2 \\divides a + b$. Trivial using $a_1=a$ and $b_1=b$.
\\item Case $\\lambda^2 \\divides a + \\eta b$. Let $a_1=a$ and $b_1=\\eta b$. \\\\
By *lmm:toInteger_cube_eq_one*, we have that $a^3 + (\\eta b)^3 = a^3 + b^3 = u c^3$.\\\\
By properties of coprimes and *lmm:eta_isUnit*, we have that
$\\gcd(a,b)=1$ implies that $\\gcd(a,\\eta b)=1$.\\\\
Since $a_1=a$, we already know that $\\lambda \\notdivides a = a_1$.\\\\
By contradiction we assume that $\\lambda \\divides b_1 = \\eta b$, which,
by *lmm:toInteger_cube_eq_one*, it implies that $\\lambda \\divides \\eta^2 \\eta b = b$
that contradicts our assumption, forcing us to conclude that $\\lambda \\notdivides b_1$.
\\item Case $\\lambda^2 \\divides a + \\eta^2 b$. Let $a_1=a$ and $b_1=\\eta^2 b$. \\\\
By *lmm:toInteger_cube_eq_one*, we have that $a^3 + (\\eta^2 b)^3 = a^3 + b^3 = u c^3$.\\\\
By properties of coprimes and *lmm:eta_isUnit*, we have that
$\\gcd(a,b)=1$ implies that $\\gcd(a,\\eta^2 b)=1$.\\\\
Since $a_1=a$, we already know that $\\lambda \\notdivides a = a_1$.\\\\
By contradiction we assume that $\\lambda \\divides b_1 = \\eta^2 b$, which,
by *lmm:toInteger_cube_eq_one*, it implies that $\\lambda \\divides \\eta \\eta^2 b = b$
that contradicts our assumption, forcing us to conclude that $\\lambda \\notdivides b_1$.
\\end\u007bitemize\u007d
Therefore, we can conclude that
$\\exists a_1,b_1 \\in \\cc\u007bO\u007d_k$ such that $S_1=(a_1,b_1,c,u)$ is a $solution$."
  rcases _root_.lambda_sq_dvd_or_dvd_or_dvd S with (h | h | h)
  · exact ⟨S.a, S.b, S.H, S.coprime, S.ha, S.hb, h⟩
  · refine ⟨S.a, η * S.b, ?_, ?_, S.ha, fun ⟨x, hx⟩ ↦ S.hb ⟨η ^ 2 * x, ?_⟩, h⟩
    · rw [mul_pow, _root_.hζ.toInteger_cube_eq_one, one_mul, S.H]
    · exact (isCoprime_mul_unit_left_right _root_.hζ.eta_isUnit _ _).2 S.coprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ S.b, mul_assoc, ← pow_succ',
        _root_.hζ.toInteger_cube_eq_one, mul_one]
  · refine ⟨S.a, η ^ 2 * S.b, ?_, ?_, S.ha, fun ⟨x, hx⟩ ↦ S.hb ⟨η * x, ?_⟩, h⟩
    · rw [mul_pow, ← pow_mul, mul_comm 2, pow_mul, _root_.hζ.toInteger_cube_eq_one, one_pow, one_mul, S.H]
    · exact (isCoprime_mul_unit_left_right (_root_.hζ.eta_isUnit.pow _) _ _).2 S.coprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ S.b, mul_assoc, ← pow_succ,
        _root_.hζ.toInteger_cube_eq_one, mul_one]

NewTheorem isCoprime_mul_unit_left_right
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
