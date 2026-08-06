import LeanCompCert.Ports.Section413G2Generated10000Chunks.Chunk00
import LeanCompCert.Ports.Section413G2Generated10000Chunks.Chunk01

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells
open LeanCompCert.Ports.Section413G2TableProgram
open LeanCompCert.Ports.Section413G2TableApplications
open LeanCompCert.Ports.Section413G2Generated10000Chunks

def chunkWords : Array (Array (UInt64 × UInt64)) := #[words00, words01]
def wordAt (X : Nat) : UInt64 × UInt64 :=
  if X = 0 then (0, 0) else chunkWords[(X - 1) / 100]![(X - 1) % 100]!
def words : Array (UInt64 × UInt64) :=
  (List.range 101).toArray.map wordAt
def expected : Array Cell := cellsOfWords words

example (i : Nat) (hi : i < 100) :
    wordAt (100 + i + 1) = words01[i]! := by
  rw [wordAt]
  rw [show 100 + i + 1 - 1 = 100 + i by omega]
  have hdiv : (100 + i) / 100 = 1 := by omega
  have hmod : (100 + i) % 100 = i := by omega
  rw [hdiv, hmod]
  rfl

example : hmTableSegment expected 0 100 =
    (29062179925628175741462, 1454670077449666781) := by
  rw [hmTableSegment_eq_local expected cells00 0 100]
  · exact total00
  · intro i hi
    have hword : wordAt (i + 1) = words00[i]! := by
      rw [wordAt]
      rw [show i + 1 - 1 = i by omega, Nat.div_eq_of_lt hi,
        Nat.mod_eq_of_lt hi]
      rfl
    have hwords : i < words00.size := by simpa [words00] using hi
    have hleft : i + 1 <
        (Array.map
          (fun p : UInt64 × UInt64 =>
            ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))
          (Array.map wordAt (List.range 101).toArray)).size := by
      simp
      omega
    have hright : i <
        (Array.map
          (fun p : UInt64 × UInt64 =>
            ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))
          words00).size := by
      simpa using hwords
    simp only [Nat.zero_add, expected, words, cells00, cellsOfWords]
    rw [getElem!_pos
          (Array.map
            (fun p : UInt64 × UInt64 =>
              ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))
            (Array.map wordAt (List.range 101).toArray))
          (i + 1) hleft,
      getElem!_pos
          (Array.map
            (fun p : UInt64 × UInt64 =>
              ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))
            words00)
          i hright,
      Array.getElem_map, Array.getElem_map, List.getElem_toArray]
    have hword' : wordAt (i + 1) = words00[i] :=
      hword.trans (getElem!_pos words00 i hwords)
    simp [hword']
