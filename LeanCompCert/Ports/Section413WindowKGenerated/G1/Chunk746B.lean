import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk746A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk746B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk746A

def state06 : KState := ⟨⟨362489953040350579, 362490036180721110⟩, ⟨(-361244002345237526), (-357052140686064302)⟩, true⟩

def words05 : List Nat := [371285253728620972, 371285253739779276, 371285253928839600, 371285253931407462, 371285253900197631, 371285253834466384, 371285253788503842, 371285253791337655, 371285253802549825, 371285253869465086]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481166189844986, 362481249353408600⟩, ⟨294815672593492239, 299009265964936033⟩, true⟩

def words06 : List Nat := [371285253917497614, 371285253920110491, 371285253884901077, 371285253954266886, 371285254065702151, 371285254068271752, 371285253972599771, 371285253878002493, 371285253782397440, 371285253763023773]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469070023042048, 362469153209752329⟩, ⟨1198160613990260973, 1202355935840697567⟩, true⟩

def words07 : List Nat := [371285253815124389, 371285253921942163, 371285254027190561, 371285254029759239, 371285253895960806, 371285253789076179, 371285253721958742, 371285253724527471, 371285253528698300, 371285253316016934]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473724430909086, 362473807640660000⟩, ⟨850520479530205825, 854717522170586255⟩, true⟩

def words08 : List Nat := [371285253102181495, 371285252960294219, 371285252729709364, 371285252549987705, 371285252369503727, 371285252172024180, 371285251754508198, 371285251517409929, 371285251278951620, 371285251174227688]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485029154114843, 362485112387235520⟩, ⟨6112496090549443, 10311284335745401⟩, true⟩

def words09 : List Nat := [371285251022955465, 371285250870273882, 371285250731429637, 371285250734261780, 371285250668304247, 371285250658269716, 371285250647378336, 371285250600913565, 371285250421830578, 371285250423170403]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk746B
