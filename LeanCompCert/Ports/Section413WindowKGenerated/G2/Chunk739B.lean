import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk739A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk739B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk739A

def state06 : KState := ⟨⟨360557397738187646, 360557433147856653⟩, ⟨1843519654810681018, 1845288546342807838⟩, true⟩

def words05 : List Nat := [360582383331316885, 360582383625118415, 360582383778887397, 360582383798705247, 360582383799600722, 360582383693979336, 360582383588056362, 360582383536535724, 360582383302209776, 360582382965952148]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575197945542464, 360575233365158947⟩, ⟨527003154810643970, 528772782105686052⟩, true⟩

def words06 : List Nat := [360582382629464971, 360582382475841073, 360582382562319034, 360582382658589704, 360582382659559797, 360582382599641377, 360582382431347410, 360582382236166000, 360582382040694333, 360582381841326390]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571018918855047, 360571054348489185⟩, ⟨836163528016257911, 837933896367720297⟩, true⟩

def words07 : List Nat := [360582381745633519, 360582381557698432, 360582381369567112, 360582381449851538, 360582381450738905, 360582381412198025, 360582381373525377, 360582381243756465, 360582380992627307, 360582380840735302]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584301456442851, 360584336896000670⟩, ⟨(-146607734941082418), (-144836632387783962)⟩, true⟩

def words08 : List Nat := [360582380688485814, 360582380685056640, 360582380555101667, 360582380276402818, 360582379997537244, 360582379672924655, 360582379510875237, 360582379497921059, 360582379484861183, 360582379406138555]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587052086291921, 360587087535775849⟩, ⟨(-350168587710836218), (-348396750674912176)⟩, true⟩

def words09 : List Nat := [360582379518292029, 360582379630749990, 360582379870909560, 360582379928774502, 360582379929745012, 360582379831585907, 360582379733244416, 360582379524695700, 360582379470486525, 360582379535199169]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk739B
