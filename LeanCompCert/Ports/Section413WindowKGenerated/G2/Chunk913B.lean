import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk913A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk913B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk913A

def state06 : KState := ⟨⟨360548879327784401, 360548934255664349⟩, ⟨3016255155042919523, 3019643816855462097⟩, true⟩

def words05 : List Nat := [360581987900935178, 360581987952790872, 360581987953967498, 360581987927492610, 360581987781171555, 360581987551359169, 360581987321181385, 360581987060312719, 360581986759435138, 360581986399018722]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585587882014336, 360585642822351711⟩, ⟨(-337632285459218037), (-334242485473249271)⟩, true⟩

def words06 : List Nat := [360581986038310662, 360581985770797086, 360581985562972237, 360581985454973220, 360581985346844542, 360581985136906939, 360581984908289028, 360581984799710935, 360581984700316477, 360581984741719200]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580117473673840, 360580172426605421⟩, ⟨162228613283563014, 165619564062091720⟩, true⟩

def words07 : List Nat := [360581984742918531, 360581984684693843, 360581984686293369, 360581984824869508, 360581984880122006, 360581984935584016, 360581984936785300, 360581984889461775, 360581984871766768, 360581984853439106]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585005202526459, 360585060167889076⟩, ⟨(-284483338873740041), (-281091252085905677)⟩, true⟩

def words08 : List Nat := [360581984934442652, 360581984935763155, 360581984917146320, 360581984832728097, 360581984748115826, 360581984580562582, 360581984483516561, 360581984495587626, 360581984496764604, 360581984468399128]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594013476395885, 360594068454235949⟩, ⟨(-1107770726968995175), (-1104377499804140197)⟩, true⟩

def words09 : List Nat := [360581984584207656, 360581984700430861, 360581984935812549, 360581985051911103, 360581985067792588, 360581985083764048, 360581985219052319, 360581985414762151, 360581985548055200, 360581985681620725]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk913B
