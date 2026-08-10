import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk971A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk971B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk971A

def state06 : KState := ⟨⟨362490731590455569, 362490875282997261⟩, ⟨(-548022162350561544), (-538596234303128412)⟩, true⟩

def words05 : List Nat := [371285332080498169, 371285332085733944, 371285332133089574, 371285332136501215, 371285332064780448, 371285331966239149, 371285331870174765, 371285331873931847, 371285331884313998, 371285331945296917]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485852479531439, 362485996202809801⟩, ⟨(-73978176102326208), (-64549261521028114)⟩, true⟩

def words06 : List Nat := [371285332003457656, 371285332006885355, 371285331999214105, 371285332023129592, 371285332077255358, 371285332080672140, 371285332025309496, 371285331952203778, 371285331906836553, 371285331917565016]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485563963308621, 362485707717243805⟩, ⟨(-45888872297055561), (-36456978634703383)⟩, true⟩

def words07 : List Nat := [371285332032729779, 371285332149260203, 371285332251630033, 371285332295934359, 371285332343107542, 371285332391980152, 371285332545056602, 371285332558043969, 371285332564454908, 371285332572116314]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489268185239521, 362489411969753801⟩, ⟨(-405866383238651685), (-396431517745153887)⟩, true⟩

def words08 : List Nat := [371285332622259325, 371285332626052831, 371285332714410182, 371285332809380907, 371285332889801444, 371285332893211788, 371285332874695578, 371285332921407175, 371285333033022467, 371285333078521639]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490435967682470, 362490579783309327⟩, ⟨(-519353040605264268), (-509915151133693104)⟩, true⟩

def words09 : List Nat := [371285333123381114, 371285333169399057, 371285333310213534, 371285333403283318, 371285333501013210, 371285333600002228, 371285333697808785, 371285333701224681, 371285333738335856, 371285333796630860]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk971B
