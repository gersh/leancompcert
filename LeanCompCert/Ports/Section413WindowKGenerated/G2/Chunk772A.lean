import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk772A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575264046704599, 360575302757413498⟩, ⟨527893188735419911, 529911613719459619⟩, true⟩

def state01 : KState := ⟨⟨360581160877224666, 360581199598340876⟩, ⟨72642528870313000, 74661757352620632⟩, true⟩

def words00 : List Nat := [360582166888032495, 360582167051412517, 360582167158296335, 360582167265372481, 360582167266388505, 360582167230270267, 360582167026685450, 360582166873790869, 360582166720583002, 360582166594291565]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360576118327058623, 360576157058679209⟩, ⟨462032181706466809, 464052221281111333⟩, true⟩

def words01 : List Nat := [360582166582759722, 360582166462358452, 360582166387680367, 360582166552311361, 360582166674684030, 360582166797235633, 360582166798234385, 360582166791584322, 360582166617493909, 360582166540954282]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566727132598291, 360566765874579456⟩, ⟨1187210151511037131, 1189230991182871039⟩, true⟩

def words02 : List Nat := [360582166464024424, 360582166410889562, 360582166190414639, 360582165886306972, 360582165582009083, 360582165234896771, 360582164988888397, 360582164833266635, 360582164677537570, 360582164437199978]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580305878685240, 360580344631086166⟩, ⟨138304712737088487, 140326357177763937⟩, true⟩

def words03 : List Nat := [360582164238732050, 360582163894414502, 360582163549786737, 360582163248596665, 360582162898838375, 360582162410468017, 360582161921899262, 360582161601013274, 360582161411068495, 360582161388688157]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589884084170134, 360589922847062721⟩, ⟨(-601661994836399655), (-599639539967979921)⟩, true⟩

def words04 : List Nat := [360582161366149565, 360582161260012663, 360582161164326726, 360582161200900824, 360582161201839408, 360582161122522592, 360582160993006683, 360582160780567777, 360582160567920171, 360582160623402601]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk772A
