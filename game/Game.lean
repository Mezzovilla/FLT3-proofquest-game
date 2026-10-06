import Game.Levels.Preliminaries
import Game.Levels.ThirdCyclotomicExtensions
import Game.Levels.FermatSLastTheoremForExponent3

Title "FLT3-proofquest-game"
Introduction "
Prove the theorems of this project, level by level, following its blueprint.
"

Info "
This game was generated automatically by
[proofquest](https://github.com/Mezzovilla/proofquest) from the project's
leanblueprint.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "FLT3-proofquest-game"
CaptionLong "A game generated from a leanblueprint dependency graph, where you
prove the theorems of the original project guided by its LaTeX write-up."

Dependency Preliminaries → FermatSLastTheoremForExponent3
Dependency Preliminaries → ThirdCyclotomicExtensions
Dependency ThirdCyclotomicExtensions → FermatSLastTheoremForExponent3

/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
