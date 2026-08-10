import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk610A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476889317262862, 362476943946456008⟩, ⟨507945697536855922, 510196618258225234⟩, true⟩

def state01 : KState := ⟨⟨362498207254484447, 362498261902177219⟩, ⟨(-792487785316554083), (-790235736024049513)⟩, true⟩

def words00 : List Nat := [371285307821708349, 371285307824007632, 371285308050668719, 371285308280379329, 371285308455501668, 371285308457584303, 371285308698286026, 371285308954942318, 371285309339210531, 371285309553649511]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479348106418605, 362479402772954360⟩, ⟨358261263666028645, 360514462664533733⟩, true⟩

def words01 : List Nat := [371285309768264229, 371285309983575406, 371285310290819472, 371285310465138602, 371285310719248468, 371285310974162109, 371285311166802408, 371285311168870348, 371285311003280021, 371285310909019004]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486416973494721, 362486471658458208⟩, ⟨(-73091681286705630), (-70837357732153940)⟩, true⟩

def words02 : List Nat := [371285310964665677, 371285310966743596, 371285310863041821, 371285310759121851, 371285310654386232, 371285310633791029, 371285310660355329, 371285310809604234, 371285310958986638, 371285310980151575]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498599450400804, 362498654154100603⟩, ⟨(-816623343389004283), (-814367876261948785)⟩, true⟩

def words03 : List Nat := [371285311269392089, 371285311559712993, 371285311959054219, 371285312001112923, 371285312017801755, 371285312035107738, 371285312277783189, 371285312387220742, 371285312607208723, 371285312828167838]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485183130759097, 362485237853111199⟩, ⟨2347882106559277, 4604487865304797⟩, true⟩

def words04 : List Nat := [371285313047382393, 371285313049454190, 371285313179752744, 371285313380998789, 371285313629999403, 371285313632068485, 371285313552531247, 371285313392793586, 371285313272318360, 371285313274697855]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk610A
