import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk739

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

def state06 : KState := ⟨⟨360557397738187646, 360557433147856653⟩, ⟨1843519654810681018, 1845288546342807838⟩, true⟩

def words05 : List Nat := [360582383331316885, 360582383625118415, 360582383778887397, 360582383798705247, 360582383799600722, 360582383693979336, 360582383588056362, 360582383536535724, 360582383302209776, 360582382965952148]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575197945542464, 360575233365158947⟩, ⟨527003154810643970, 528772782105686052⟩, true⟩

def words06 : List Nat := [360582382629464971, 360582382475841073, 360582382562319034, 360582382658589704, 360582382659559797, 360582382599641377, 360582382431347410, 360582382236166000, 360582382040694333, 360582381841326390]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571018918855047, 360571054348489185⟩, ⟨836163528016257911, 837933896367720297⟩, true⟩

def words07 : List Nat := [360582381745633519, 360582381557698432, 360582381369567112, 360582381449851538, 360582381450738905, 360582381412198025, 360582381373525377, 360582381243756465, 360582380992627307, 360582380840735302]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584301456442851, 360584336896000670⟩, ⟨(-146607734941082418), (-144836632387783962)⟩, true⟩

def words08 : List Nat := [360582380688485814, 360582380685056640, 360582380555101667, 360582380276402818, 360582379997537244, 360582379672924655, 360582379510875237, 360582379497921059, 360582379484861183, 360582379406138555]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587052086291921, 360587087535775849⟩, ⟨(-350168587710836218), (-348396750674912176)⟩, true⟩

def words09 : List Nat := [360582379518292029, 360582379630749990, 360582379870909560, 360582379928774502, 360582379929745012, 360582379831585907, 360582379733244416, 360582379524695700, 360582379470486525, 360582379535199169]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk739
