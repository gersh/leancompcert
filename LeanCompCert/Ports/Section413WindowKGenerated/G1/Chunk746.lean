import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk746

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496868855694656, 362496951857359057⟩, ⟨(-877148009884410342), (-872966499878370046)⟩, true⟩

def state01 : KState := ⟨⟨362498592901051080, 362498675925874458⟩, ⟨(-1005811887535498987), (-1001628649748382529)⟩, true⟩

def words00 : List Nat := [371285250207561366, 371285250210144748, 371285250352541598, 371285250502217176, 371285250687454760, 371285250738453044, 371285250787251077, 371285250836939198, 371285251064995361, 371285251247881289]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 74600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 74600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482146081205903, 362482229129143432⟩, ⟨221428472543758687, 225613434994160429⟩, true⟩

def words01 : List Nat := [371285251608990866, 371285251971116044, 371285252254741428, 371285252299626474, 371285252398657425, 371285252498977857, 371285252700226204, 371285252702792743, 371285252664929229, 371285252627334188]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 74610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 74600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490632722882091, 362490715793780960⟩, ⟨(-411837892040578306), (-407651216098770348)⟩, true⟩

def words02 : List Nat := [371285252705336277, 371285252735172974, 371285252943305319, 371285253152533746, 371285253340433424, 371285253343000284, 371285253310917195, 371285253333478716, 371285253494237198, 371285253570092429]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 74620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 74600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487674730567285, 362487757824870909⟩, ⟨(-191054565895997460), (-186866143138406528)⟩, true⟩

def words03 : List Nat := [371285253645408446, 371285253721618583, 371285253915416451, 371285254045442911, 371285254142837461, 371285254241175462, 371285254337997581, 371285254340565370, 371285254255964200, 371285254292721844]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 74630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 74600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475860425456395, 362475943542663905⟩, ⟨690823823486430233, 695013955905969969⟩, true⟩

def words04 : List Nat := [371285254403138961, 371285254405706445, 371285254277139450, 371285254148881164, 371285254019665962, 371285253946486839, 371285253842443221, 371285253849355123, 371285253851274432, 371285253843479793]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 74640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 74600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk746
