/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Reduction.AddressMachineLoopLemmas

namespace OAI

/-! The addressed producer writes the single-orbit codec directly. Both endpoint
templates use the same canonical address space, so neither doubled serialization
nor a second physical postprocessing machine is needed. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

open Turing UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity

namespace SingleAddress


end SingleAddress

abbrev output := MachineAddressGame.output

noncomputable def computableInPolyTime (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) :=
  MachineAddressGame.computableInPolyTime k T

theorem workAlphabetFinite (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d)
    (tape : (computableInPolyTime k T).tm.K) :
    Finite ((computableInPolyTime k T).tm.Γ tape) :=
  MachineAddressGame.workAlphabetFinite k T tape

end UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

end OAI
