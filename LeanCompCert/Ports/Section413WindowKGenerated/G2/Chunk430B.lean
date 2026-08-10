import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk430A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk430B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk430A

def state06 : KState := ⟨⟨360580376352703933, 360580387842694561⟩, ⟨113586736652035333, 113921096112513829⟩, true⟩

def words05 : List Nat := [360583028054694964, 360583029158935781, 360583029971024959, 360583030961283566, 360583031747205898, 360583032533256946, 360583033304710942, 360583033539236398, 360583033539760010, 360583033478925693]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360623528360452205, 360623539855984471⟩, ⟨(-1744769038323056536), (-1744434440212589182)⟩, true⟩

def words06 : List Nat := [360583033475383083, 360583033803566342, 360583034670932418, 360583035538380700, 360583035870012554, 360583035870599968, 360583036361854985, 360583036877516396, 360583037546571845, 360583038487541375]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630082674125975, 360630094175258629⟩, ⟨(-2027183800880704521), (-2026848961533810139)⟩, true⟩

def words07 : List Nat := [360583039019391486, 360583039551271838, 360583040314787863, 360583041348308275, 360583042245992103, 360583043143733455, 360583043746842716, 360583044591682487, 360583045684302661, 360583046777066066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360626991716017840, 360627003222677621⟩, ⟨(-1894010182722258624), (-1893675105238514462)⟩, true⟩

def words08 : List Nat := [360583048244922133, 360583049555272872, 360583050594471369, 360583051633680898, 360583052303311171, 360583053306555904, 360583054390640704, 360583055474784472, 360583056248171573, 360583057268644563]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360658158493787587, 360658170006006111⟩, ⟨(-3237115110081850611), (-3236779793045585743)⟩, true⟩

def words09 : List Nat := [360583058605020179, 360583059941524980, 360583061816357891, 360583063409361024, 360583064509876006, 360583065610381802, 360583067083954209, 360583068963287265, 360583070706254495, 360583072449266231]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk430B
