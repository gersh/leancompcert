import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk821A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk821B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk821A

def state06 : KState := ⟨⟨362491021247571432, 362491122676061384⟩, ⟨(-488873550174572633), (-483246543178353399)⟩, true⟩

def words05 : List Nat := [371285240113992970, 371285240222906953, 371285240478428853, 371285240537367654, 371285240571532275, 371285240606568423, 371285240752334943, 371285240825346552, 371285240898914604, 371285240973755201]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487885842795160, 362487987296963685⟩, ⟨(-231310691507554121), (-225681574628278279)⟩, true⟩

def words06 : List Nat := [371285241028298260, 371285241031144528, 371285240891111441, 371285240897592053, 371285240948111335, 371285240951007431, 371285240878849106, 371285240800474161, 371285240773344071, 371285240810068938]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481742115346920, 362481843595153314⟩, ⟨273601018622065708, 279232242295194314⟩, true⟩

def words07 : List Nat := [371285240993563571, 371285241178186527, 371285241339238230, 371285241342084934, 371285241330013654, 371285241343086072, 371285241468710215, 371285241471564716, 371285241445907398, 371285241407787717]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490804563755398, 362490906069012893⟩, ⟨(-471181148152776545), (-465547832775261885)⟩, true⟩

def words08 : List Nat := [371285241389290012, 371285241392427442, 371285241436448767, 371285241534660791, 371285241607871519, 371285241610734962, 371285241593976368, 371285241612702711, 371285241778040317, 371285241849904046]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494093054999594, 362494194586231169⟩, ⟨(-741448620938037987), (-735813170621042191)⟩, true⟩

def words09 : List Nat := [371285241920807798, 371285241992730010, 371285242211513505, 371285242390744316, 371285242580218570, 371285242770747749, 371285242960051959, 371285242973405371, 371285243084246473, 371285243196702806]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk821B
