import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk827A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk827B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk827A

def state06 : KState := ⟨⟨362506141956457833, 362506244929460658⟩, ⟨(-1740282749834567724), (-1734528381587618436)⟩, true⟩

def words05 : List Nat := [371285285575820209, 371285285641976247, 371285285781097243, 371285285824093183, 371285285842305545, 371285285861369911, 371285286025359278, 371285286135716054, 371285286390909504, 371285286647400417]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495878114360021, 362495981113284520⟩, ⟨(-890842219530808062), (-885085705877707092)⟩, true⟩

def words06 : List Nat := [371285286870414760, 371285286899491129, 371285287073700962, 371285287249425794, 371285287468370024, 371285287529326525, 371285287580042214, 371285287631817357, 371285287794726789, 371285287927194251]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473051262413161, 362473154287109414⟩, ⟨998701004300963596, 1004459651217638296⟩, true⟩

def words07 : List Nat := [371285288155509896, 371285288384952392, 371285288592916099, 371285288607013056, 371285288609080238, 371285288599723661, 371285288647515206, 371285288650384516, 371285288516643473, 371285288373256040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490463287222285, 362490566337656132⟩, ⟨(-442707541076528684), (-436946763473452500)⟩, true⟩

def words08 : List Nat := [371285288228621621, 371285288231290816, 371285288243280367, 371285288305279168, 371285288342799016, 371285288345689204, 371285288349399097, 371285288426670137, 371285288562440391, 371285288629167608]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492592953051464, 362492696029686876⟩, ⟨(-619013674806390369), (-613250727849636709)⟩, true⟩

def words09 : List Nat := [371285288694974227, 371285288761754161, 371285288973290024, 371285289113279988, 371285289275261069, 371285289438363598, 371285289578508429, 371285289581378584, 371285289616291010, 371285289709378551]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk827B
