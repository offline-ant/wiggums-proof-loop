/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

namespace UniqueGamesTheorem.Reduction.MachineReverse

open Turing

/-- Reversal is transfer with the identity symbol map, with the same `X + 1`
transition bound. No separate reversal machine or execution induction is needed. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id List.reverse := by
  simpa only [List.map_id] using
    MachineTransfer.computableInPolyTime (id : Bool → Bool) false

end UniqueGamesTheorem.Reduction.MachineReverse

end OAI
