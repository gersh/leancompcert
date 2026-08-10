import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk917A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk917B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk917A

def state06 : KState := ⟨⟨362486669111286752, 362486796710202400⟩, ⟨(-163714714291283278), (-155809434378065182)⟩, true⟩

def words05 : List Nat := [371285099500852756, 371285099367932611, 371285099233323596, 371285099218469597, 371285099088900083, 371285098940773145, 371285098791309591, 371285098761908878, 371285098696150678, 371285098718306300]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483302821287329, 362483430449177018⟩, ⟨145156154570675186, 153064093287927888⟩, true⟩

def words06 : List Nat := [371285098739698827, 371285098742928875, 371285098675885299, 371285098659962435, 371285098659119067, 371285098662334703, 371285098560021898, 371285098458877405, 371285098356401012, 371285098359096251]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471725605146934, 362471853261861661⟩, ⟨1207707409087013023, 1215617993225116797⟩, true⟩

def words07 : List Nat := [371285098443577340, 371285098547507696, 371285098623564171, 371285098626771721, 371285098544442791, 371285098499490830, 371285098452866654, 371285098455999944, 371285098314255605, 371285098173533323]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479344924648885, 362479472610057933⟩, ⟨508398890638515117, 516312108487838051⟩, true⟩

def words08 : List Nat := [371285098031398474, 371285098009289962, 371285097926311324, 371285097919491284, 371285097911560622, 371285097881931512, 371285097693114897, 371285097612972387, 371285097534380526, 371285097537702425]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476797391842754, 362476925106590503⟩, ⟨742236149180028930, 750152060166506786⟩, true⟩

def words09 : List Nat := [371285097478888174, 371285097403703611, 371285097327186121, 371285097300165319, 371285097212668004, 371285097132428337, 371285097051136264, 371285096959146326, 371285096782613960, 371285096697659855]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk917B
