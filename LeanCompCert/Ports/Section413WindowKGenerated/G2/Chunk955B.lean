import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk955A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk955B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk955A

def state06 : KState := ⟨⟨360572079919038736, 360572140223891726⟩, ⟨956582615854854230, 960473899493479942⟩, true⟩

def words05 : List Nat := [360582190080125600, 360582190453420700, 360582190771220813, 360582190979965856, 360582191140575482, 360582191301548237, 360582191370227138, 360582191371612359, 360582191331191422, 360582191227444400]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597502890529990, 360597563208456864⟩, ⟨(-1472977034855194496), (-1469084501811369886)⟩, true⟩

def words06 : List Nat := [360582191127755257, 360582191189072609, 360582191282405601, 360582191376021177, 360582191377300513, 360582191368575584, 360582191280968331, 360582191281632324, 360582191390530923, 360582191552810158]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595400818966659, 360595461150120756⟩, ⟨(-1272088432667420459), (-1268194635434247599)⟩, true⟩

def words07 : List Nat := [360582191612356743, 360582191672018908, 360582191797853528, 360582192001672382, 360582192177631388, 360582192353818208, 360582192474752379, 360582192598494631, 360582192738443447, 360582192878859374]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595680308006140, 360595740652201079⟩, ⟨(-1298833647902269482), (-1294938604161595040)⟩, true⟩

def words08 : List Nat := [360582193128288625, 360582193268847844, 360582193347664540, 360582193426632280, 360582193431132089, 360582193497592784, 360582193641227046, 360582193785125905, 360582193850838583, 360582193993999349]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604463811260126, 360604524168539703⟩, ⟨(-2138510310483817627), (-2134614015916433979)⟩, true⟩

def words09 : List Nat := [360582194173745998, 360582194353919665, 360582194622744785, 360582194782718876, 360582194850302702, 360582194917993022, 360582195094873798, 360582195333905377, 360582195568610506, 360582195803607156]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk955B
