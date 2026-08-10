import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk229A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk229B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk229A

def state06 : KState := ⟨⟨360544615629423609, 360544618726846736⟩, ⟨823440475031644518, 823488590209574872⟩, true⟩

def words05 : List Nat := [360580484382270569, 360580486800565026, 360580487767243933, 360580487900761045, 360580487901010279, 360580487549794434, 360580487198524090, 360580487119838051, 360580486516516004, 360580484954643321]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599591574115377, 360599594674346308⟩, ⟨(-438831517544211753), (-438783337884994941)⟩, true⟩

def words06 : List Nat := [360580483722847039, 360580485240912589, 360580488650521234, 360580492059889710, 360580493850976651, 360580493851274400, 360580493759532816, 360580492818668767, 360580492221365805, 360580493053263857]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566113811286415, 360566116914353855⟩, ⟨330488896403419835, 330537141231378311⟩, true⟩

def words07 : List Nat := [360580493053531266, 360580492559522667, 360580493461530811, 360580496362363760, 360580498753515103, 360580501144506493, 360580502126420389, 360580502126718349, 360580501227571745, 360580500601961835]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360536846015573274, 360536849121451889⟩, ⟨1002850183940132541, 1002898493382748647⟩, true⟩

def words08 : List Nat := [360580499976312476, 360580498996585209, 360580496136286876, 360580492106789237, 360580488077591641, 360580483564709958, 360580480022662301, 360580477873294599, 360580475724076461, 360580472370402857]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574644832236507, 360574647940926372⟩, ⟨133656486396936330, 133704860484258870⟩, true⟩

def words09 : List Nat := [360580470473238767, 360580469955845912, 360580470807537378, 360580470807835544, 360580470298133973, 360580468021291590, 360580465744591824, 360580463123313758, 360580461448181916, 360580461195730036]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk229B
