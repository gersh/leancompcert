import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk721A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490060410927084, 362490137737229050⟩, ⟨(-355972498557434354), (-352207319921605824)⟩, true⟩

def state01 : KState := ⟨⟨362502525163731905, 362502602512142773⟩, ⟨(-1254688179124510163), (-1250921406321284421)⟩, true⟩

def words00 : List Nat := [371285253082925761, 371285253258213238, 371285253624588900, 371285253991983278, 371285254300555077, 371285254393219136, 371285254565750875, 371285254739531500, 371285255104140862, 371285255347267494]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362506280340406033, 362506357711385788⟩, ⟨(-1525469446026074388), (-1521701045666487676)⟩, true⟩

def words01 : List Nat := [371285255587447274, 371285255828478883, 371285256217389032, 371285256544207129, 371285256928216923, 371285257313159791, 371285257695973484, 371285257843258281, 371285258137503752, 371285258433149679]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486362697232373, 362486440090298622⟩, ⟨(-88905958149461406), (-85135964800859030)⟩, true⟩

def words02 : List Nat := [371285258808037511, 371285258927569955, 371285259031271469, 371285259135800631, 371285259291970300, 371285259353523741, 371285259493408478, 371285259634372469, 371285259774901359, 371285259793826913]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500782945413643, 362500860360800194⟩, ⟨(-1129127409291784829), (-1125355805863792923)⟩, true⟩

def words03 : List Nat := [371285259934276049, 371285260075972744, 371285260379250375, 371285260427292680, 371285260429259863, 371285260421427513, 371285260503898166, 371285260530945053, 371285260748867950, 371285260967863254]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482703226383143, 362482780664148531⟩, ⟨175244623656505876, 179017841604523286⟩, true⟩

def words04 : List Nat := [371285261184505175, 371285261241666953, 371285261439714318, 371285261639100196, 371285261881791594, 371285261884267361, 371285261871117286, 371285261859283103, 371285261851072134, 371285261853914360]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk721A
