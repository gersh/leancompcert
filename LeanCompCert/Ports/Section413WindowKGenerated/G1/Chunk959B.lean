import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk959A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk959B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk959A

def state06 : KState := ⟨⟨362499839151152090, 362499979182453236⟩, ⟨(-1421526848952575426), (-1412454455348012954)⟩, true⟩

def words05 : List Nat := [371285259393510052, 371285259525208968, 371285259678358898, 371285259687712694, 371285259690315591, 371285259683771960, 371285259774346140, 371285259822726898, 371285259978398482, 371285260135597243]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486433024608182, 362486573086309086⟩, ⟨(-135056307142014686), (-125980996217864776)⟩, true⟩

def words06 : List Nat := [371285260285760795, 371285260291939303, 371285260341944139, 371285260393644772, 371285260455150853, 371285260458531912, 371285260416509908, 371285260376142194, 371285260370136282, 371285260387720785]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476321512973701, 362476461604910537⟩, ⟨835454054036516333, 844532266857717795⟩, true⟩

def words07 : List Nat := [371285260512412320, 371285260638441669, 371285260762849572, 371285260766215998, 371285260765853107, 371285260768612656, 371285260813114821, 371285260816482059, 371285260737084761, 371285260649157857]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493844094356018, 362493984216411708⟩, ⟨(-846444480528697640), (-837363376745825914)⟩, true⟩

def words08 : List Nat := [371285260559765697, 371285260554201584, 371285260541371473, 371285260584229498, 371285260611629901, 371285260615018655, 371285260581347275, 371285260621717311, 371285260769057264, 371285260863422930]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494036016442270, 362494176169247155⟩, ⟨(-864863241755760969), (-855779186208849649)⟩, true⟩

def words09 : List Nat := [371285260936403863, 371285261010524823, 371285261173124331, 371285261282780500, 371285261419567996, 371285261557612714, 371285261675093671, 371285261703348323, 371285261798495723, 371285261895581164]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk959B
