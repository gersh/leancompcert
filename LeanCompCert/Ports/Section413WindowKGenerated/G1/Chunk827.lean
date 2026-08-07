import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk827

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497087934463615, 362497190752464479⟩, ⟨(-990433733824717913), (-984692188902592335)⟩, true⟩

def state01 : KState := ⟨⟨362480122079066297, 362480224922946776⟩, ⟨412707931823171743, 418451617122033329⟩, true⟩

def words00 : List Nat := [371285284243851274, 371285284246717460, 371285284281059936, 371285284368651932, 371285284434865292, 371285284437745387, 371285284363976195, 371285284285760217, 371285284206409708, 371285284185637165]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471951354801211, 362472054224552440⟩, ⟨1088604217872986497, 1094350043067938971⟩, true⟩

def words01 : List Nat := [371285284196922017, 371285284270620790, 371285284340603462, 371285284343470133, 371285284218476807, 371285284127844782, 371285284078317017, 371285284081184491, 371285283951353551, 371285283794705583]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498121473070617, 362498224368460796⟩, ⟨(-1076289780744184057), (-1070541834562762873)⟩, true⟩

def words02 : List Nat := [371285283636720135, 371285283626168123, 371285283624874191, 371285283699439839, 371285283752452412, 371285283755375943, 371285283818013178, 371285283924944294, 371285284176509448, 371285284335890626]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487505450479489, 362487608372007049⟩, ⟨(-197965395845527640), (-192215287187204696)⟩, true⟩

def words03 : List Nat := [371285284460529263, 371285284586106847, 371285284752671754, 371285284847553592, 371285284985954872, 371285285125488890, 371285285254270110, 371285285257139054, 371285285244335295, 371285285275994345]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479490498245301, 362479593445290322⟩, ⟨465271925375275528, 471024145483298444⟩, true⟩

def words04 : List Nat := [371285285427351626, 371285285448986530, 371285285469617176, 371285285491241414, 371285285530281343, 371285285533471916, 371285285523770142, 371285285550979751, 371285285577005930, 371285285579978942]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk827
