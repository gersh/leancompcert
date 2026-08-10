import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk545A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk545B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk545A

def state06 : KState := ⟨⟨360595927011980402, 360595945819706873⟩, ⟨(-775896570436633473), (-775203250242533097)⟩, true⟩

def words05 : List Nat := [360581739290490542, 360581739213601328, 360581739170397202, 360581739171155146, 360581738870630931, 360581738284470813, 360581737698186040, 360581737362044938, 360581737548200858, 360581737809402031]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574263284979332, 360574282099916610⟩, ⟨406011990512773321, 406705704164092925⟩, true⟩

def words06 : List Nat := [360581737853834049, 360581737854592122, 360581737607883866, 360581737652695479, 360581737653340950, 360581737467395131, 360581736946354229, 360581736210908784, 360581735475343570, 360581735017346775]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360540800588601890, 360540819410689167⟩, ⟨2232256508032919124, 2232950611895382704⟩, true⟩

def words07 : List Nat := [360581734881391332, 360581734705579827, 360581734529678887, 360581734185969660, 360581733744993743, 360581733104360862, 360581732463521374, 360581732157945668, 360581731676744891, 360581730927946320]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360590929554035113, 360590948383278759⟩, ⟨(-503963202677308307), (-503268708184531663)⟩, true⟩

def words08 : List Nat := [360581730179003422, 360581729765365914, 360581729787513571, 360581729966554383, 360581729967260146, 360581729858628453, 360581729771667930, 360581729537394401, 360581729318412490, 360581729488072873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360558472951369322, 360558491787846421⟩, ⟨1267973740849897930, 1268668630251682594⟩, true⟩

def words09 : List Nat := [360581729488749036, 360581729463908766, 360581729438939036, 360581729239032847, 360581729216405983, 360581729055308189, 360581728894133530, 360581728565315488, 360581727901729911, 360581727477045170]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk545B
