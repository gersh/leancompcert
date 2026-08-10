import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk652A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk652A
