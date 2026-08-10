import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk695A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk695B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk695A

def state06 : KState := ⟨⟨360591838698449077, 360591869868027939⟩, ⟨(-640260394073558891), (-638795873763768043)⟩, true⟩

def words05 : List Nat := [360582685775156083, 360582685965462967, 360582686187864143, 360582686259187538, 360582686260095652, 360582686154875070, 360582686149430325, 360582686354734409, 360582686487569087, 360582686620608211]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585138478546255, 360585169657509626⟩, ⟨(-174321589646475860), (-172856416504380630)⟩, true⟩

def words06 : List Nat := [360582686621862603, 360582686622847208, 360582686417496239, 360582686273336152, 360582686128908433, 360582685933043238, 360582685743073663, 360582685450170186, 360582685157086815, 360582685053055121]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556187929981319, 360556219118234640⟩, ⟨1839942984457136368, 1841408803947007874⟩, true⟩

def words07 : List Nat := [360582685202651632, 360582685352431611, 360582685353324417, 360582685341762114, 360582685203006861, 360582684894082501, 360582684584873449, 360582684399686080, 360582684125374053, 360582683746057966]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567997903963411, 360568029101507717⟩, ⟨1018197847755187125, 1019664313759555115⟩, true⟩

def words08 : List Nat := [360582683366513766, 360582683058248098, 360582682853817648, 360582682814755209, 360582682775617513, 360582682560213663, 360582682315200929, 360582682066647705, 360582681817806770, 360582681556081069]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580578431421376, 360580609638345929⟩, ⟨142641324438164580, 144108443259625096⟩, true⟩

def words09 : List Nat := [360582681346407812, 360582681033881230, 360582680721175160, 360582680664866806, 360582680665692038, 360582680630281264, 360582680594780721, 360582680373416123, 360582680190579433, 360582680161955982]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk695B
