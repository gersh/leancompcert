import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk310A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk310B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk310A

def state06 : KState := ⟨⟨360510699521096519, 360510705340786099⟩, ⟨2242943356702646003, 2243065595532257619⟩, true⟩

def words05 : List Nat := [360582927893648935, 360582929042382213, 360582929390524511, 360582929390937222, 360582928704598025, 360582927755827713, 360582926806999457, 360582926164811868, 360582924845028590, 360582922520294543]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360633178156258972, 360633183979844903⟩, ⟨(-1561909037817649354), (-1561786677947994300)⟩, true⟩

def words06 : List Nat := [360582920195617071, 360582918612388675, 360582917684913658, 360582917737417993, 360582917737799433, 360582916970536895, 360582916263318637, 360582916255065862, 360582917269472031, 360582918887702778]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598980985105295, 360598986812628004⟩, ⟨(-499345674288172649), (-499223192083492115)⟩, true⟩

def words07 : List Nat := [360582919991497582, 360582921095266388, 360582921831846024, 360582923091956572, 360582923663755900, 360582924235584142, 360582924286411868, 360582924286825092, 360582924289881283, 360582924807155739]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583694294566280, 360583700125977493⟩, ⟨(-24156228229182170), (-24033625149991032)⟩, true⟩

def words08 : List Nat := [360582926355088578, 360582926870456906, 360582926870826688, 360582926717769556, 360582926564654123, 360582926563395961, 360582926949775853, 360582927336204525, 360582927336572838, 360582927116902520]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360630567437147357, 360630573272458637⟩, ⟨(-1481713696904347870), (-1481590972552646806)⟩, true⟩

def words09 : List Nat := [360582928172319982, 360582929227790379, 360582930130632825, 360582931071794271, 360582931143764582, 360582931215761538, 360582931375922554, 360582932158716497, 360582933690919455, 360582935223117695]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk310B
