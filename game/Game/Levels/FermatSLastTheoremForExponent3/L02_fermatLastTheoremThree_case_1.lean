import Game.Metadata
import Game.Levels.FermatSLastTheoremForExponent3.L01_cube_of_not_dvd

World "FermatSLastTheoremForExponent3"
Level 2

Title "Fermat's Last Theorem for 3: Case 1"

Introduction "
Let $a, b, c \\in \\N$. \\\\
Let $3 \\notdivides abc$. \\\\\\\\
Then $a ^ 3 + b ^ 3 \\neq c ^ 3$.
"

section
open ZMod

/-- Let $a, b, c \in \N$. \\
Let $3 \notdivides abc$. \\\\
Then $a ^ 3 + b ^ 3 \neq c ^ 3$. -/
TheoremDoc fermatLastTheoremThree_case_1 as "fermatLastTheoremThree_case_1" in "Fermat's Last Theorem for Exponent 3"

Statement fermatLastTheoremThree_case_1 {a b c : ℕ} (hdvd : ¬ 3 ∣ a * b * c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  Hint "By hypothesis we know that $3 \\notdivides abc$, which implies that $3 \\notdivides a$, $3 \\notdivides b$ and $3 \\notdivides c$. \\\\
By repeatedly applying *lmm:cube_of_not_dvd* for each case,
we can conclude that $$a ^ 3 + b ^ 3 \\neq c ^ 3.$$"
  simp_rw [Nat.prime_three.dvd_mul, not_or] at hdvd
  apply mt (congrArg (Nat.cast : ℕ → ZMod 9))
  simp_rw [Nat.cast_add, Nat.cast_pow]
  rcases _root_.cube_of_not_dvd hdvd.1.1 with ha | ha <;>
  rcases _root_.cube_of_not_dvd hdvd.1.2 with hb | hb <;>
  rcases _root_.cube_of_not_dvd hdvd.2 with hc | hc <;>
  rw [ha, hb, hc] <;> decide

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
