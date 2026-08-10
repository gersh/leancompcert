import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk799A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk799B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk799A

def state06 : KState := ⟨⟨362469437740831518, 362469533610240641⟩, ⟨1245567726064232088, 1250744083454219352⟩, true⟩

def words05 : List Nat := [371285176301955727, 371285176319516458, 371285176323280426, 371285176326092082, 371285176199890778, 371285176123095145, 371285176086635017, 371285176089398572, 371285175924841293, 371285175732344871]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477249529851798, 362477345424041127⟩, ⟨620884211489137349, 626062550428007217⟩, true⟩

def words06 : List Nat := [371285175538630181, 371285175410725840, 371285175203521918, 371285175101084925, 371285174997835299, 371285174871080724, 371285174535082293, 371285174356907645, 371285174177195303, 371285174141690596]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478204089465899, 362478300008775808⟩, ⟨544553813194257871, 549734161151861537⟩, true⟩

def words07 : List Nat := [371285174045870320, 371285173930315907, 371285173851386457, 371285173854464034, 371285173815915373, 371285173787487764, 371285173758088967, 371285173726978563, 371285173486681570, 371285173404139048]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476108468625912, 362476204412586019⟩, ⟨712189550336247396, 717371869946724596⟩, true⟩

def words08 : List Nat := [371285173320088868, 371285173317984094, 371285173213863251, 371285173110475937, 371285173006001133, 371285172914571844, 371285172743884760, 371285172730503517, 371285172716260275, 371285172681994030]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504178110248092, 362504274079236944⟩, ⟨(-1533251376021457301), (-1528067054241300161)⟩, true⟩

def words09 : List Nat := [371285172578175895, 371285172587985472, 371285172738306131, 371285172761916797, 371285172764056684, 371285172762580615, 371285172911602991, 371285172997268146, 371285173237907106, 371285173479816421]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk799B
