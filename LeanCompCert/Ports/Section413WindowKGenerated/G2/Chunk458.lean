import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk458

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598856490769418, 360598869555589059⟩, ⟨(-717953421807486532), (-717549068754776868)⟩, true⟩

def state01 : KState := ⟨⟨360576646619658496, 360576659690468013⟩, ⟨299173244735404133, 299577872154137623⟩, true⟩

def words00 : List Nat := [360583202887995554, 360583202861357121, 360583202359023629, 360583202227094632, 360583202095000721, 360583201842156204, 360583201324163554, 360583200567418154, 360583199810575953, 360583199264188907]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360534092119376748, 360534105196097901⟩, ⟨2248862536540642669, 2249267434800860173⟩, true⟩

def words01 : List Nat := [360583199310166098, 360583199499009233, 360583199499568770, 360583199449701137, 360583198924419372, 360583197893061767, 360583196861564275, 360583196305653773, 360583195473166137, 360583194402444494]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599380441902140, 360599393524560729⟩, ⟨(-742860366552408701), (-742455196209560123)⟩, true⟩

def words02 : List Nat := [360583193331626901, 360583192736411025, 360583192750343257, 360583192995347093, 360583192995929804, 360583192832978669, 360583192846383907, 360583193091164917, 360583193323251457, 360583193677378483]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609425087702325, 360609438176340739⟩, ⟨(-1203266085815276882), (-1202860641387050250)⟩, true⟩

def words03 : List Nat := [360583193792901058, 360583193908488838, 360583194499088550, 360583195328784385, 360583195948656127, 360583196568614023, 360583196830870935, 360583197187280320, 360583197760236476, 360583198333375118]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596712785404855, 360596725879970306⟩, ⟨(-620522326353797064), (-620116610201677192)⟩, true⟩

def words04 : List Nat := [360583199381271428, 360583199954532943, 360583200097677117, 360583200240873694, 360583200241399830, 360583200368525956, 360583200699811466, 360583201031205865, 360583201031768204, 360583201276140473]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360604302571296666, 360604315671787683⟩, ⟨(-968538677634054715), (-968132689763801093)⟩, true⟩

def words05 : List Nat := [360583201709598338, 360583202143218974, 360583203051370473, 360583203642217635, 360583203827580758, 360583204012979409, 360583204185998443, 360583204597776713, 360583205058625902, 360583205519593798]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360637012571466027, 360637025677946317⟩, ⟨(-2468989800474177410), (-2468583537906903528)⟩, true⟩

def words06 : List Nat := [360583205742486322, 360583205752952717, 360583206237811397, 360583206722855012, 360583207087020342, 360583207556705994, 360583207788456595, 360583208020265692, 360583208726322060, 360583209900267459]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597356155602464, 360597369268006714⟩, ⟨(-649776681759879041), (-649370147431016983)⟩, true⟩

def words07 : List Nat := [360583211061855824, 360583212223505419, 360583213148049520, 360583213598626023, 360583213912713740, 360583214226953534, 360583214679116574, 360583215293355046, 360583215602415371, 360583215911553476]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360619865008017845, 360619878126358605⟩, ⟨(-1682722185998284986), (-1682315379273015288)⟩, true⟩

def words08 : List Nat := [360583216101603930, 360583216532237262, 360583217122163580, 360583217712183212, 360583217867353796, 360583217867982941, 360583217704025338, 360583217859491978, 360583218387650898, 360583219187148891]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602036082558797, 360602049206903136⟩, ⟨(-864369576377936224), (-863962494119843272)⟩, true⟩

def words09 : List Nat := [360583219747383055, 360583220307671409, 360583221341689293, 360583222614048295, 360583223678082330, 360583224742172508, 360583225568514478, 360583226083277820, 360583226493885474, 360583226904684888]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk458
