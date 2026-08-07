import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk652

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360558055048966054, 360558082292868151⟩, ⟨1620204206070379924, 1621404115287608146⟩, true⟩

def state01 : KState := ⟨⟨360590157958290680, 360590185210861600⟩, ⟨(-473036207919039295), (-471835733452644585)⟩, true⟩

def words00 : List Nat := [360582950073480619, 360582949881923605, 360582949967692469, 360582950128528419, 360582950129400309, 360582950058129374, 360582949752195469, 360582949638133354, 360582949575292608, 360582949687200675]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570917461482752, 360570944722807100⟩, ⟨781832078927200325, 783033124248943413⟩, true⟩

def words01 : List Nat := [360582949688019110, 360582949682126080, 360582949903940780, 360582950250893381, 360582950538754790, 360582950826757205, 360582950996908974, 360582950997827666, 360582950933511382, 360582950750471144]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360560609986141327, 360560637256119571⟩, ⟨1454035923105631548, 1455237532878309246⟩, true⟩

def words02 : List Nat := [360582950567135956, 360582950362885089, 360582949924156804, 360582949367724953, 360582948811160558, 360582948193090669, 360582947755905025, 360582947420704601, 360582947085415200, 360582946585153426]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579148491434254, 360579175770091842⟩, ⟨244560327856120053, 245762503825473385⟩, true⟩

def words03 : List Nat := [360582946243892354, 360582945899299419, 360582945554450175, 360582945203986319, 360582944801195367, 360582944198738665, 360582943596124307, 360582943170898013, 360582942879346898, 360582942822572307]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573920338232428, 360573947625649530⟩, ⟨585511388236779460, 586714135718345146⟩, true⟩

def words04 : List Nat := [360582942765663708, 360582942532320182, 360582942064515190, 360582941758894857, 360582941453040480, 360582941088561232, 360582940774065449, 360582940264642998, 360582939755060317, 360582939413170118]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360568463436240707, 360568490732311326⟩, ⟨941651161429394142, 942854473596994302⟩, true⟩

def words05 : List Nat := [360582939276111367, 360582939250391533, 360582939224566103, 360582939081265775, 360582939007786134, 360582938833449478, 360582938717899485, 360582938718818965, 360582938615533627, 360582938395100125]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580466445617682, 360580493750377099⟩, ⟨158180119430930352, 159383998671022790⟩, true⟩

def words06 : List Nat := [360582938174473625, 360582937948421407, 360582937859817582, 360582937690210445, 360582937520538814, 360582937150022119, 360582936545184330, 360582936174983481, 360582935804496380, 360582935668542735]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569469727727652, 360569497041241563⟩, ⟨875998880643744282, 877203331332971734⟩, true⟩

def words07 : List Nat := [360582935631950032, 360582935477949927, 360582935323781655, 360582935362691359, 360582935363475319, 360582935324403962, 360582935285241102, 360582935128484242, 360582934797069394, 360582934592273012]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579892958223116, 360579920280411820⟩, ⟨195533992908022647, 196739009930455191⟩, true⟩

def words08 : List Nat := [360582934387174981, 360582934354797432, 360582934328748836, 360582934170368921, 360582934011847089, 360582933699496688, 360582933617548377, 360582933694210425, 360582933695044179, 360582933590412287]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588760769102308, 360588788099972084⟩, ⟨(-383462826912828221), (-382257243059462065)⟩, true⟩

def words09 : List Nat := [360582933685053136, 360582933826111440, 360582934201033657, 360582934342186851, 360582934343043041, 360582934282651651, 360582934222066613, 360582934145790297, 360582934236184751, 360582934326782402]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk652
