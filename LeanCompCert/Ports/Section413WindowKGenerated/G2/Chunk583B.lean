import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk583A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk583B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk583A

def state06 : KState := ⟨⟨360514244044408242, 360514265680236388⟩, ⟨3951693171153138560, 3952546230535449612⟩, true⟩

def words05 : List Nat := [360581997653814403, 360581997559665675, 360581997465417260, 360581997201190415, 360581996720769925, 360581996050857717, 360581995380724375, 360581994743991593, 360581993814394157, 360581992654714378]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585917912122002, 360585939555640559⟩, ⟨(-231623750672484614), (-230770242438787604)⟩, true⟩

def words06 : List Nat := [360581991494891514, 360581990432090740, 360581989549707088, 360581988961184618, 360581988372625736, 360581987533286749, 360581986851049669, 360581986462721576, 360581986074165832, 360581986047178501]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578767530315691, 360578789181606622⟩, ⟨185718680898783472, 186572642842889924⟩, true⟩

def words07 : List Nat := [360581986047904467, 360581985968485040, 360581985888924189, 360581985774615460, 360581985775298295, 360581985743357725, 360581985711334924, 360581985414535753, 360581985066901624, 360581985013104445]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360560218935236895, 360560240594197885⟩, ⟨1268668733780730465, 1269523143542163813⟩, true⟩

def words08 : List Nat := [360581985121038944, 360581985121854147, 360581984991965253, 360581984675342617, 360581984358597387, 360581983966832128, 360581983768902106, 360581983470934941, 360581983172883483, 360581982727158018]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602823333721123, 360602845000377666⟩, ⟨(-1219158065763077887), (-1218303206619864069)⟩, true⟩

def words09 : List Nat := [360581982355462962, 360581982277438494, 360581982413643734, 360581982738412359, 360581982770833734, 360581982803319520, 360581982971030809, 360581983285369919, 360581983643254772, 360581984001308817]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk583B
