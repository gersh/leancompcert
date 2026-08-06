import LeanCompCert.Ports.Section413G1Generated99999Chunks.Aggregate
import LeanCompCert.Ports.Section413G2Generated99999Chunks.Aggregate

/-! Direct, kernel-efficient views of the generated 99,999-cell tables. -/

namespace LeanCompCert.Ports.Section413WindowDirectTables

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells (decodeZ)

def directG1 (X : Nat) : Cell :=
  if X < 100000 then
    let p := LeanCompCert.Ports.Section413G1Generated99999Chunks.wordAt X
    { lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat }
  else czero

def directG2 (X : Nat) : Cell :=
  if X < 100000 then
    let p := LeanCompCert.Ports.Section413G2Generated99999Chunks.wordAt X
    { lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat }
  else czero

theorem expectedG1_eq_direct :
    (fun X =>
      LeanCompCert.Ports.Section413G1Generated99999Chunks.expected99999[X]!) =
      directG1 := by
  funext X
  by_cases hX : X < 100000
  · simp only [LeanCompCert.Ports.Section413G1Generated99999Chunks.expected99999,
      LeanCompCert.Ports.Section413G1Generated99999Chunks.words99999,
      LeanCompCert.Ports.Section413G1TableProgram.cellsOfWords]
    rw [getElem!_pos _ _ (by simpa using hX), Array.getElem_map,
      Array.getElem_map, List.getElem_toArray]
    simp [directG1, hX]
  · have hsize :
        LeanCompCert.Ports.Section413G1Generated99999Chunks.expected99999.size =
          100000 := by
      simp [LeanCompCert.Ports.Section413G1Generated99999Chunks.expected99999,
        LeanCompCert.Ports.Section413G1Generated99999Chunks.words99999,
        LeanCompCert.Ports.Section413G1TableProgram.cellsOfWords]
    have hout :
        LeanCompCert.Ports.Section413G1Generated99999Chunks.expected99999[X]! =
          default := by
      apply getElem!_neg
      omega
    rw [hout]
    simp [directG1, hX, default, czero]

theorem expectedG2_eq_direct :
    (fun X =>
      LeanCompCert.Ports.Section413G2Generated99999Chunks.expected99999[X]!) =
      directG2 := by
  funext X
  by_cases hX : X < 100000
  · simp only [LeanCompCert.Ports.Section413G2Generated99999Chunks.expected99999,
      LeanCompCert.Ports.Section413G2Generated99999Chunks.words99999,
      LeanCompCert.Ports.Section413G2TableProgram.cellsOfWords]
    rw [getElem!_pos _ _ (by simpa using hX), Array.getElem_map,
      Array.getElem_map, List.getElem_toArray]
    simp [directG2, hX]
  · have hsize :
        LeanCompCert.Ports.Section413G2Generated99999Chunks.expected99999.size =
          100000 := by
      simp [LeanCompCert.Ports.Section413G2Generated99999Chunks.expected99999,
        LeanCompCert.Ports.Section413G2Generated99999Chunks.words99999,
        LeanCompCert.Ports.Section413G2TableProgram.cellsOfWords]
    have hout :
        LeanCompCert.Ports.Section413G2Generated99999Chunks.expected99999[X]! =
          default := by
      apply getElem!_neg
      omega
    rw [hout]
    simp [directG2, hX, default, czero]

end LeanCompCert.Ports.Section413WindowDirectTables
