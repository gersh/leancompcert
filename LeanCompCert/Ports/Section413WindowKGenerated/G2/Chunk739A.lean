import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk739A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551990870169913, 360552026220164167⟩, ⟨2241765691388376869, 2243530171168712091⟩, true⟩

def state01 : KState := ⟨⟨360590563319488583, 360590598679399752⟩, ⟨(-608917719032677262), (-607152506342687950)⟩, true⟩

def words00 : List Nat := [360582384811170619, 360582384533031837, 360582384347831387, 360582384314843472, 360582384281778748, 360582384090579833, 360582383904820846, 360582383902163017, 360582383923792632, 360582384036026741]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586029994880200, 360586065364815658⟩, ⟨(-273878887089197530), (-272112933454259536)⟩, true⟩

def words01 : List Nat := [360582384036963421, 360582384037492007, 360582384037834231, 360582384144854747, 360582384210144762, 360582384275607204, 360582384276552981, 360582384231551682, 360582384182128647, 360582384233155450]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575289658951758, 360575325038774038⟩, ⟨520106931953394848, 521873616472611484⟩, true⟩

def words02 : List Nat := [360582384382706996, 360582384447796059, 360582384448733163, 360582384396339524, 360582384343777012, 360582384262417207, 360582384263282211, 360582384233521136, 360582384203648441, 360582384062397366]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360594117422728531, 360594152812470259⟩, ⟨(-872034519311832558), (-870267101398545874)⟩, true⟩

def words03 : List Nat := [360582383967776334, 360582383793962065, 360582383619846101, 360582383508379271, 360582383402395991, 360582383141262336, 360582382879934565, 360582382765365946, 360582382901977037, 360582383062245100]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590497278145165, 360590532677921409⟩, ⟨(-604442203280037584), (-602674043368093310)⟩, true⟩

def words04 : List Nat := [360582383081924345, 360582383082982843, 360582383250950170, 360582383426975117, 360582383506256510, 360582383507307970, 360582383403891395, 360582383199907635, 360582382995707613, 360582383037708727]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk739A
