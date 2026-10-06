import Game.Metadata
import Game.Levels.ThirdCyclotomicExtensions.L23_lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd

World "FermatSLastTheoremForExponent3"
Level 1

Title "cube_of_not_dvd"

Introduction "
Let $n \\in \\N$. \\\\
Let $\\left[n \\right] \\in \\Z_9$. \\\\
Let $3 \\notdivides n$. \\\\ \\\\
Then $\\left[n \\right]^3 = 1 \\lor \\left[n \\right]^3 = 8$.
"

section
open ZMod

/-- Let $n \in \N$. \\
Let $\left[n \right] \in \Z_9$. \\
Let $3 \notdivides n$. \\ \\
Then $\left[n \right]^3 = 1 \lor \left[n \right]^3 = 8$. -/
TheoremDoc cube_of_not_dvd as "cube_of_not_dvd" in "Fermat's Last Theorem for Exponent 3"

Statement cube_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) :
    (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 := by
  Hint "By *lmm:cube_of_castHom_ne_zero*, we can conclude that $\\left[n \\right]^3 = 1 \\lor \\left[n \\right]^3 = 8$."
  apply _root_.cube_of_castHom_ne_zero
  rwa [map_natCast, Ne, Fin.nat_cast_eq_zero]

NewTactic rwa
run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
