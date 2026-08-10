import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk953A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk953B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk953A

def state06 : KState := ⟨⟨362500526875325867, 362500665094110588⟩, ⟨(-1481913677646545824), (-1473014670092904390)⟩, true⟩

def words05 : List Nat := [371285217330704075, 371285217435796736, 371285217593320716, 371285217663614395, 371285217721268195, 371285217779897806, 371285217934211435, 371285218044009783, 371285218208278158, 371285218374066829]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493143761360641, 362493282010353921⟩, ⟨(-777883034512526844), (-768981146120573834)⟩, true⟩

def words06 : List Nat := [371285218513763008, 371285218517105756, 371285218592936737, 371285218679982607, 371285218798455577, 371285218801799867, 371285218792791652, 371285218784212656, 371285218871910580, 371285218960305997]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487731338177533, 362487869617180346⟩, ⟨(-261629487722015771), (-252724737165345799)⟩, true⟩

def words07 : List Nat := [371285219148866669, 371285219338754813, 371285219527895841, 371285219589837406, 371285219656471828, 371285219724760698, 371285219889923834, 371285219921424442, 371285219951703178, 371285219983215874]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483637447914275, 362483775756865741⟩, ⟨128890490820037671, 137798098035603933⟩, true⟩

def words08 : List Nat := [371285220012896043, 371285220016680255, 371285220104650208, 371285220206174486, 371285220289998635, 371285220293343886, 371285220259103447, 371285220272300446, 371285220329334902, 371285220332796506]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486910689817846, 362487049029307865⟩, ⟨(-183335404620677371), (-174424884185055847)⟩, true⟩

def words09 : List Nat := [371285220320177427, 371285220308067156, 371285220388728703, 371285220444697857, 371285220532367993, 371285220621350614, 371285220708792265, 371285220712136208, 371285220672004903, 371285220695389090]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk953B
