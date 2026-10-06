import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L05_three_dvd_gcd_of_dvd_b_of_dvd_c

World "FermatSLastTheoremForExponent3"
Level 6

Title "fermatLastTheoremThree_of_three_dvd_only_c"

Introduction "
To prove *Fermat's Last Theorem for Exponent $3$*, it suffices to prove that
$$\\forall a, b, c \\in \\Z, \\text{ if } c \\neq 0 \\text{ and } 3 \\notdivides a \\text{ and }
3 \\notdivides b \\text{ and } 3 \\divides c \\text{ and } \\gcd(a,b)=1,
\\text{ then } a^3 + b^3 \\neq c^3.$$
Equivalently, $$\\forall a, b, c \\in \\Z, \\text{ if } c \\neq 0 \\text{ and } 3 \\notdivides a \\text{ and }
3 \\notdivides b \\text{ and } 3 \\divides c \\text{ and } \\gcd(a,b)=1,
\\text{ then } a^3 + b^3 \\neq c^3$$ implies *Fermat's Last Theorem for Exponent $3$*.
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
open Finset
open Int
open Nat

/-- To prove *Fermat's Last Theorem for Exponent $3$*, it suffices to prove that
$$\forall a, b, c \in \Z, \text{ if } c \neq 0 \text{ and } 3 \notdivides a \text{ and }
3 \notdivides b \text{ and } 3 \divides c \text{ and } \gcd(a,b)=1,
\text{ then } a^3 + b^3 \neq c^3.$$
Equivalently, $$\forall a, b, c \in \Z, \text{ if } c \neq 0 \text{ and } 3 \notdivides a \text{ and }
3 \notdivides b \text{ and } 3 \divides c \text{ and } \gcd(a,b)=1,
\text{ then } a^3 + b^3 \neq c^3$$ implies *Fermat's Last Theorem for Exponent $3$*. -/
TheoremDoc fermatLastTheoremThree_of_three_dvd_only_c as "fermatLastTheoremThree_of_three_dvd_only_c" in "Fermat's Last Theorem for Exponent 3"

Statement fermatLastTheoremThree_of_three_dvd_only_c (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b  → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    _root_.FermatLastTheoremFor 3 := by
  Hint "By contradiction we assume that
$$\\exists a,b,c \\in \\N \\smallsetminus \\set\u007b0\u007d \\text\u007b such that \u007d a^3 + b^3 = c^3.$$
By *lmm:fermatLastTheoremWith_of_fermatLastTheoremWith_coprime*
we can assume that $\\gcd(a,b,c)=1$. \\\\
By *Fermat's Last Theorem for 3: Case 1* we can assume that $3 \\divides a b c$,
from which it follows that $$(3 \\divides a) \\lor (3 \\divides b) \\lor (3 \\divides c).$$
We proceed by analysing each case:
\\begin\u007bitemize\u007d
\\item Case $3 \\divides a$. \\\\
Let $a'=-c$, $b'=b$, $c'=-a$, then $3 \\divides c'$ and
$$(a'\\neq 0) \\land (b'\\neq 0) \\land (c' \\neq 0).$$
Then $3 \\notdivides a'$ since otherwise by *lmm:three_dvd_gcd_of_dvd_a_of_dvd_c*
we would have that $3 \\divides \\gcd(a,b,c)=1$ which is absurd. \\\\
Analogously, by *lmm:three_dvd_gcd_of_dvd_a_of_dvd_b* we have that $3 \\notdivides b'$.\\\\
By contradiction we assume that $\\gcd(a',b') \\neq 1$ which, by basic divisibility properties,
implies that there is a prime $p$ such that $p \\divides a'$ and $p \\divides b'$.
It follows that $p \\divides b'^3 + a'^3 = b^3 - c^3 = -a^3$, which implies that $p \\divides a$.\\\\
Therefore $p \\divides \\gcd(a,b,c)=1$ which is absurd. \\\\
Moreover, we have that $a'^3 + b'^3 = -c^3 + b^3 = -a^3 = c'^3$ that contradicts our hypothesis.
\\item Case $3 \\divides b$. \\\\
Let $a'=a$, $b'=-c$, $c'=-b$.\\\\
The rest of the proof is analogous to the first case using *lmm:three_dvd_gcd_of_dvd_a_of_dvd_b* and
*lmm:three_dvd_gcd_of_dvd_b_of_dvd_c*.
\\item Case $3 \\divides c$.
Let $a'=a$, $b'=b$, $c'=c$.\\\\
The rest of the proof is analogous to the first case using *lmm:three_dvd_gcd_of_dvd_a_of_dvd_c* and
*lmm:three_dvd_gcd_of_dvd_b_of_dvd_c*.
\\end\u007bitemize\u007d
Therefore, we can conclude that $a^3 + b^3 \\neq c^3$."
  refine _root_.fermatLastTheoremWith_of_fermatLastTheoremWith_coprime (fun a b c ha hb hc Hgcd hF ↦?_)
  by_cases h1 : 3 ∣ a * b * c
  swap; exact _root_.fermatLastTheoremThree_case_1 h1 hF
  rw [(Nat.prime_three).dvd_mul, (Nat.prime_three).dvd_mul] at h1
  have h3 : ¬(3 ∣ 1) := by decide
  rcases h1 with ((⟨k, hk⟩ | ⟨k, hk⟩) | ⟨k, hk⟩)
  · refine H (-(c : ℤ)) b (-(a : ℤ)) (by simp [ha]) (fun hdvd ↦ h3 ?_) (fun hdvd ↦ h3 ?_) ?_ ?_ ?_
    · exact Hgcd.symm ▸ _root_.three_dvd_gcd_of_dvd_a_of_dvd_c ⟨k, hk⟩ (coe_nat_dvd.1 (dvd_neg.1 hdvd)) hF
    · exact Hgcd.symm ▸ _root_.three_dvd_gcd_of_dvd_a_of_dvd_b ⟨k, hk⟩ (by exact_mod_cast hdvd) hF
    · exact ⟨-k, by simp [hk]⟩
    · refine (isCoprime_iff_coprime.2 (coprime_of_dvd' (fun p hp hpc hpb ↦ ?_))).neg_left
      rw [← Hgcd]; refine dvd_gcd (fun x hx ↦ ?_)
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with (hx | hx | hx)
      · refine hx ▸ (hp.dvd_of_dvd_pow <| (Nat.dvd_add_iff_right (m := b ^ 3) (n := a ^ 3)
          (dvd_pow hpb (by decide))).2 ?_)
        rw [add_comm, hF]
        exact dvd_pow hpc (by decide)
      · exact hx ▸ hpb
      · exact hx ▸ hpc
    · rw [Odd.neg_pow (by decide), Odd.neg_pow (by decide), add_comm, ← sub_eq_add_neg,
        sub_eq_iff_eq_add, add_comm, ← sub_eq_add_neg, eq_sub_iff_add_eq, add_comm]
      exact_mod_cast hF
  · refine H a (-(c : ℤ)) ((-(b : ℤ))) (by simp [hb]) (fun hdvd ↦ h3 ?_) (fun hdvd ↦ h3 ?_) ?_ ?_ ?_
    · exact Hgcd.symm ▸ _root_.three_dvd_gcd_of_dvd_a_of_dvd_b (by exact_mod_cast hdvd) ⟨k, hk⟩ hF
    · exact Hgcd.symm ▸ _root_.three_dvd_gcd_of_dvd_b_of_dvd_c ⟨k, hk⟩ (coe_nat_dvd.1 (dvd_neg.1 hdvd)) hF
    · exact ⟨-k, by simp [hk]⟩
    · refine (Nat.isCoprime_iff_coprime.2 (coprime_of_dvd' (fun p hp hpa hpc ↦ ?_))).neg_right
      rw [← Hgcd]; refine dvd_gcd (fun x hx ↦ ?_)
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with (hx | hx | hx)
      · exact hx ▸ hpa
      · exact hx ▸ (hp.dvd_of_dvd_pow <| (Nat.dvd_add_iff_right (m := a ^ 3) (n := b ^ 3)
          (dvd_pow hpa (by decide))).2 (hF ▸ dvd_pow hpc (by decide)))
      · exact hx ▸ hpc
    · rw [Odd.neg_pow (by decide), Odd.neg_pow (by decide), ← sub_eq_add_neg, sub_eq_iff_eq_add,
        add_comm, ← sub_eq_add_neg, eq_sub_iff_add_eq]
      exact_mod_cast hF
  · refine H a b c (by simp [hc]) (fun hdvd ↦ h3 ?_) (fun hdvd ↦ h3 ?_) ?_ ?_ ?_
    · exact Hgcd.symm ▸ _root_.three_dvd_gcd_of_dvd_a_of_dvd_c (by exact_mod_cast hdvd) ⟨k, hk⟩ hF
    · exact Hgcd.symm ▸ _root_.three_dvd_gcd_of_dvd_b_of_dvd_c (by exact_mod_cast hdvd) ⟨k, hk⟩ hF
    · exact ⟨k, by simp [hk]⟩
    · refine isCoprime_iff_coprime.2 (coprime_of_dvd' (fun p hp hpa hpb ↦ ?_))
      rw [← Hgcd]; refine dvd_gcd (fun x hx ↦ ?_)
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with (hx | hx | hx)
      · exact hx ▸ hpa
      · exact hx ▸ hpb
      · refine hx ▸ hp.dvd_of_dvd_pow (n := 3) ?_
        exact hF.symm ▸ dvd_add (dvd_pow hpa (by decide)) (dvd_pow hpb (by decide))
    · exact_mod_cast hF

NewTactic by_cases
NewDefinition FermatLastTheoremFor
NewTheorem dvd_neg Nat.isCoprime_iff_coprime Nat.coprime_of_dvd'
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
