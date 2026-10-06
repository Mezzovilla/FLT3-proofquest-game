import Game.Generated.Defs

/-- The `simpa` tactic. -/
TacticDoc simpa

/-- `intro x` introduces a variable or hypothesis from the goal. -/
TacticDoc intro

/-- The `let` tactic. -/
TacticDoc «let»

/-- The `obtain` tactic. -/
TacticDoc obtain

/-- `simp` simplifies the goal using simp lemmas. -/
TacticDoc simp

/-- `rw [h]` rewrites the goal using the equality `h`. -/
TacticDoc rw

/-- The `refine` tactic. -/
TacticDoc refine

/-- `have h : t := e` introduces a new hypothesis `h : t` proved by `e`. -/
TacticDoc «have»

/-- The `dsimp` tactic. -/
TacticDoc dsimp

/-- `rfl` proves goals of the form `a = a` (definitional equality). -/
TacticDoc rfl

/-- `apply t` matches the goal against the conclusion of `t` and creates goals for its hypotheses. -/
TacticDoc apply

/-- The `congr` tactic. -/
TacticDoc congr

/-- The `infer_instance` tactic. -/
TacticDoc infer_instance

/-- The `norm_cast` tactic. -/
TacticDoc norm_cast

/-- The `rcases` tactic. -/
TacticDoc rcases

/-- The `left` tactic. -/
TacticDoc left

/-- The `right` tactic. -/
TacticDoc right

/-- The `show` tactic. -/
TacticDoc «show»

/-- The `linarith` tactic. -/
TacticDoc linarith

/-- The `norm_num` tactic. -/
TacticDoc norm_num

/-- `exact e` closes the goal if `e` is a proof of it. -/
TacticDoc exact

/-- The `ring` tactic. -/
TacticDoc ring

/-- The `ext` tactic. -/
TacticDoc ext

/-- The `suffices` tactic. -/
TacticDoc «suffices»

/-- The `calc` tactic. -/
TacticDoc «calc»

/-- The `contradiction` tactic. -/
TacticDoc contradiction

/-- The `rwa` tactic. -/
TacticDoc rwa

/-- The `exact_mod_cast` tactic. -/
TacticDoc exact_mod_cast

/-- The `by_cases` tactic. -/
TacticDoc by_cases

/-- The `by_contra` tactic. -/
TacticDoc by_contra

/-- The `use` tactic. -/
TacticDoc use

/-- The `tauto` tactic. -/
TacticDoc tauto

/-- `omega` solves linear arithmetic goals over `Nat` and `Int`. -/
TacticDoc omega

/-- `unfold f` unfolds the definition of `f` in the goal. -/
TacticDoc unfold

/-- The `ring_nf` tactic. -/
TacticDoc ring_nf

/-- `constructor` splits a goal built from a structure (like `∧`) into one goal per field. -/
TacticDoc constructor
