import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L02_fermatLastTheoremThree_case_1

World "FermatSLastTheoremForExponent3"
Level 3

Title "three_dvd_gcd_of_dvd_a_of_dvd_b"

Introduction "
Let $a, b, c \\in \\N$. \\\\
Let $3 \\divides a$ and $3 \\divides b$. \\\\
Let $a ^ 3 + b ^ 3 = c ^ 3$. \\\\\\\\
Then $3 \\divides \\gcd(a,b,c)$.
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

/-- Let $a, b, c \in \N$. \\
Let $3 \divides a$ and $3 \divides b$. \\
Let $a ^ 3 + b ^ 3 = c ^ 3$. \\\\
Then $3 \divides \gcd(a,b,c)$. -/
TheoremDoc three_dvd_gcd_of_dvd_a_of_dvd_b as "three_dvd_gcd_of_dvd_a_of_dvd_b" in "Fermat's Last Theorem for Exponent 3"

Statement three_dvd_gcd_of_dvd_a_of_dvd_b {a b c : ℕ} (ha : 3 ∣ a) (hb : 3 ∣ b)
    (hF : a ^ 3 + b ^ 3 = c ^ 3) : 3 ∣ ({a, b, c} : Finset ℕ).gcd id := by
  Hint "By hypothesis we have that $3 \\divides a^3 + b^3 = c^3$, which implies that $3 \\divides c$,
from which we can conclude that $3 \\divides \\gcd(a,b,c)$."
  have hc : 3 ∣ c := by
    have : 3 ∣ (c : ℤ) ^ 3 := by
      replace hF : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = (c : ℤ) ^ 3 := by exact_mod_cast hF
      rw [← hF]
      exact dvd_add (dvd_pow (by exact_mod_cast ha) (by decide))
        (dvd_pow (by exact_mod_cast hb) (by decide))
    exact Int.coe_nat_dvd.1 <| Int.prime_three.dvd_of_dvd_pow this
  refine Finset.dvd_gcd (fun x hx ↦ ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (hx | hx | hx)
  · exact hx ▸ ha
  · exact hx ▸ hb
  · exact hx ▸ hc

NewTactic exact_mod_cast
NewTheorem dvd_pow Finset.dvd_gcd
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
