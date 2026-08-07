import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk552

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489234119082734, 362489278499634708⟩, ⟨(-242323193224674777), (-240668251564895291)⟩, true⟩

def state01 : KState := ⟨⟨362487658688668267, 362487703085763234⟩, ⟨(-155269153733394421), (-153613298812665187)⟩, true⟩

def words00 : List Nat := [371284919054493469, 371284919190213027, 371284919326003774, 371284919462400047, 371284919674427940, 371284919723887205, 371284920100217430, 371284920477305559, 371284920738272874, 371284920790589942]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362520212153308406, 362520256567179551⟩, ⟨(-1952737280442084480), (-1951080499225113686)⟩, true⟩

def words01 : List Nat := [371284921006577789, 371284921223493151, 371284921767087083, 371284921970987523, 371284922121377788, 371284922272392531, 371284922750180577, 371284923064511730, 371284923705639927, 371284924347566993]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496412518547271, 362496456949190255⟩, ⟨(-638496239501911449), (-636838532059690911)⟩, true⟩

def words02 : List Nat := [371284924982021422, 371284925180197868, 371284925465032287, 371284925750842352, 371284926117672143, 371284926119530398, 371284926098818416, 371284926052211394, 371284926283770794, 371284926494698038]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467009425361257, 362467053872732063⟩, ⟨985647219988486893, 987305851395459423⟩, true⟩

def words03 : List Nat := [371284926873004556, 371284927252070475, 371284927583459575, 371284927585317797, 371284927480050509, 371284927475571254, 371284927539095489, 371284927540954136, 371284927218288385, 371284926896834081]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362497817335358836, 362497861799383202⟩, ⟨(-716312969367980223), (-714653417936099995)⟩, true⟩

def words04 : List Nat := [371284926574549357, 371284926507128077, 371284926498198996, 371284926658797278, 371284926758799217, 371284926760660549, 371284926525518837, 371284926546602064, 371284926893950612, 371284927130002809]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501157015836287, 362501201496793446⟩, ⟨(-900878851870205129), (-899218364813980213)⟩, true⟩

def words05 : List Nat := [371284927301782518, 371284927474132893, 371284927814020099, 371284927990650666, 371284928239123210, 371284928488313865, 371284928729285117, 371284928731176436, 371284928994223524, 371284929290991634]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484246448472720, 362484290945978922⟩, ⟨33725577860382713, 35386979502421021⟩, true⟩

def words06 : List Nat := [371284929879852940, 371284930033197793, 371284930190607190, 371284930348670950, 371284930521551456, 371284930545885020, 371284930773639375, 371284931002121688, 371284931200604138, 371284931202528632]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500130223088073, 362500174737452543⟩, ⟨(-844214724823570952), (-842552391343084946)⟩, true⟩

def words07 : List Nat := [371284931423647801, 371284931657359002, 371284932164479954, 371284932318087188, 371284932360117265, 371284932402705097, 371284932731666145, 371284932917246978, 371284933194251399, 371284933472074872]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496940257006374, 362496984788137093⟩, ⟨(-667915748430988404), (-666252488025660836)⟩, true⟩

def words08 : List Nat := [371284933749690050, 371284933751549853, 371284933776974907, 371284933922947041, 371284934167657647, 371284934232400416, 371284934296022709, 371284934360273396, 371284934641535996, 371284934861602474]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480902757231743, 362480947305121000⟩, ⟨218962313880446437, 220626500947469925⟩, true⟩

def words09 : List Nat := [371284935407524204, 371284935954168290, 371284936433641890, 371284936477987762, 371284936621426162, 371284936765828889, 371284937073871104, 371284937075732351, 371284937004469074, 371284936934432890]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk552
