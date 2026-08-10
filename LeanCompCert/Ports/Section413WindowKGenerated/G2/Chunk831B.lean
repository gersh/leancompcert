import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk831A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk831B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk831A

def state06 : KState := ⟨⟨360586961362864508, 360587006542983243⟩, ⟨(-382369584936186493), (-379832187427673399)⟩, true⟩

def words05 : List Nat := [360582438158123243, 360582438295002395, 360582438427748309, 360582438633162724, 360582438801879900, 360582438970787597, 360582439056980846, 360582439058173515, 360582439054954016, 360582439111285360]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575369348239296, 360575414539577357⟩, ⟨581660988935826464, 584199319501526990⟩, true⟩

def words06 : List Nat := [360582439210559205, 360582439220061839, 360582439221126857, 360582439142129914, 360582439062937094, 360582438947714173, 360582438913926259, 360582438866377273, 360582438818707622, 360582438698763380]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607018225467136, 360607063428061982⟩, ⟨(-2050788671942911719), (-2048249405093577793)⟩, true⟩

def words07 : List Nat := [360582438615279798, 360582438554386255, 360582438518033521, 360582438604926538, 360582438606028031, 360582438571494324, 360582438645459132, 360582438828246817, 360582439125251068, 360582439422518726]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602304644908513, 360602349858882500⟩, ⟨(-1658762359459549769), (-1656222146038986205)⟩, true⟩

def words08 : List Nat := [360582439586547980, 360582439786831550, 360582440105566588, 360582440424644366, 360582440684954683, 360582440801302521, 360582440821818003, 360582440842467565, 360582440948444576, 360582441189122082]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578339455780742, 360578384680987999⟩, ⟨335029647978704581, 337570795953313029⟩, true⟩

def words09 : List Nat := [360582441497273351, 360582441805644493, 360582442004154265, 360582442058656358, 360582442059672365, 360582442015505772, 360582442043824434, 360582442068746353, 360582442069809563, 360582442022285515]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk831B
