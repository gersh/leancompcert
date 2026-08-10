import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk625A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk625B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk625A

def state06 : KState := ⟨⟨360536690411858999, 360536715411426018⟩, ⟨2875469072251152509, 2876525591287665961⟩, true⟩

def words05 : List Nat := [360582698330400052, 360582698435115468, 360582698435898385, 360582698382861850, 360582698074942247, 360582697702396876, 360582697329606358, 360582696946843282, 360582696413906741, 360582695679828954]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571192798453045, 360571217806308253⟩, ⟨716885612033095774, 717942649619619532⟩, true⟩

def words06 : List Nat := [360582694945572059, 360582694399330784, 360582693980306601, 360582693816758193, 360582693653147002, 360582693247630545, 360582692929560496, 360582692607236935, 360582692284653847, 360582692037563162]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360546285654376476, 360546310670602208⟩, ⟨2275470618474850825, 2276528179846485157⟩, true⟩

def words07 : List Nat := [360582691854966276, 360582691543954083, 360582691232796219, 360582690911363269, 360582690717068258, 360582690457313384, 360582690197480339, 360582689757519801, 360582689138076444, 360582688557784159]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562513272013273, 360562538296510360⟩, ⟨1259885996946654967, 1260944075980405303⟩, true⟩

def words08 : List Nat := [360582687977201528, 360582687651947601, 360582687362459714, 360582686909232332, 360582686455876133, 360582685938004730, 360582685591296681, 360582685237925353, 360582684884470032, 360582684391349479]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617935869499570, 360617960902282047⟩, ⟨(-2209297725857863525), (-2208239128199928323)⟩, true⟩

def words09 : List Nat := [360582684070190951, 360582684004361774, 360582684046542392, 360582684271521597, 360582684282234779, 360582684293004686, 360582684558618544, 360582684951712855, 360582685515936956, 360582686080343102]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk625B
