import Game.Metadata
import Game.Levels.Preliminaries.L02_fermatLastTheoremWith_of_fermatLastTheoremWith_coprime

World "Preliminaries"
Level 3

Title "cube_of_castHom_ne_zero"

Introduction "
Let $\\Z_9$ be the ring of integers modulo $9$. \\\\
Let $\\Z_3$ be the ring of integers modulo $3$. \\\\
Let $n \\in \\Z_9$. \\\\
Let $\\phi : \\Z_9 \\to \\Z_3$ be the canonical ring homomorphism. \\\\
Let $\\phi(n) \\neq 0$. \\\\ \\\\
Then $n^3=1 \\lor n^3=8$.
"

section
open ZMod

/-- Let $\Z_9$ be the ring of integers modulo $9$. \\
Let $\Z_3$ be the ring of integers modulo $3$. \\
Let $n \in \Z_9$. \\
Let $\phi : \Z_9 \to \Z_3$ be the canonical ring homomorphism. \\
Let $\phi(n) \neq 0$. \\ \\
Then $n^3=1 \lor n^3=8$. -/
TheoremDoc cube_of_castHom_ne_zero as "cube_of_castHom_ne_zero" in "Preliminaries"

Statement cube_of_castHom_ne_zero {n : ZMod 9} :
    castHom (show 3 ∣ 9 by norm_num) (ZMod 3) n ≠ 0 → n ^ 3 = 1 ∨ n ^ 3 = 8 := by
  Hint "This has already been formalised and included in \\href\u007bhttps://pitmonticone.github.io/FLT3/docs/FLT3/Mathlib/NumberTheory/FLT/Three.html#cube_of_castHom_ne_zero\u007d\u007bMathlib\u007d."
  fin_cases n <;> decide

run_cmd _root_.ProofQuest.completeInventory _root_.ProofQuest.exerciseNames

end

Conclusion "Level completed! 🎉"
