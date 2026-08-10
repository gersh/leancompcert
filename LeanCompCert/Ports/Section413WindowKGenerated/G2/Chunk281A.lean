import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk281A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360626878611724777, 360626883334209667⟩, ⟨(-1253211916830531367), (-1253122162663310485)⟩, true⟩

def state01 : KState := ⟨⟨360610957810993982, 360610962537005323⟩, ⟨(-806194606843297938), (-806104753565334456)⟩, true⟩

def words00 : List Nat := [360582290366699221, 360582290367069624, 360582289866112778, 360582290085826102, 360582290086143701, 360582289115329397, 360582288465045418, 360582287135847028, 360582285806672500, 360582286760492025]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564077263578960, 360564081993086697⟩, ⟨512033046534004990, 512122998113007862⟩, true⟩

def words01 : List Nat := [360582289043406766, 360582291326236215, 360582292973901508, 360582293361620513, 360582293424917855, 360582293488315049, 360582294289359474, 360582294695451869, 360582294695789444, 360582294048496122]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360665645099646193, 360665649832651075⟩, ⟨(-2344515996910592746), (-2344425946974696424)⟩, true⟩

def words02 : List Nat := [360582293616632068, 360582294576043636, 360582296796479583, 360582299016828515, 360582300162840625, 360582301659007845, 360582303342357260, 360582305025693348, 360582307281716912, 360582310244759614]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360634536410688095, 360634541147231240⟩, ⟨(-1469335697578437204), (-1469245548093922450)⟩, true⟩

def words03 : List Nat := [360582312574128198, 360582314903373350, 360582317199905903, 360582320149870716, 360582322315314592, 360582324480664167, 360582325973405782, 360582327295685048, 360582329151488780, 360582331007289734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582556698255482, 360582561438290127⟩, ⟨(-6371390522187388), (-6281142768984126)⟩, true⟩

def words04 : List Nat := [360582333802079263, 360582335339257896, 360582336057699697, 360582336776127712, 360582336787338964, 360582337433816786, 360582338048297889, 360582338662801324, 360582338663134275, 360582338315034507]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk281A
