import LeanCompCert.Ports.Section413WindowRuntime

/-! Small structural lemmas kept separate from the generated trace shards. -/

namespace LeanCompCert.Ports.Section413WindowTraceLemmas

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime

theorem trace_words_length (G : Nat → Cell) (v lo : Nat)
    (boundNum : Int) (offset start len : Nat) (p : KState) :
    (trace G v lo boundNum offset start len p).2.length = len := by
  induction len generalizing start p with
  | zero => rfl
  | succ len ih =>
      simp only [trace, List.length_cons]
      rw [ih]

end LeanCompCert.Ports.Section413WindowTraceLemmas
