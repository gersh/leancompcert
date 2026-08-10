import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk245A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk245B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk245A

def state06 : KState := ⟨⟨360692244229798874, 360692247795277341⟩, ⟨(-2669961848687403237), (-2669902607979863987)⟩, true⟩

def words05 : List Nat := [360583510273629251, 360583514521747842, 360583519767877701, 360583523367082862, 360583525574757208, 360583527782282298, 360583530468050578, 360583533978652408, 360583538405370131, 360583542831799476]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593862477202891, 360593866045741069⟩, ⟨(-253697868142426943), (-253638552274404053)⟩, true⟩

def words06 : List Nat := [360583546430534526, 360583548383455323, 360583549167459327, 360583549951487031, 360583549951756038, 360583549777464503, 360583548543863256, 360583546292140020, 360583544040538847, 360583543366473868]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360535126224053452, 360535129795605487⟩, ⟨1190066006851089364, 1190125396785596384⟩, true⟩

def words07 : List Nat := [360583545441953883, 360583547517326093, 360583548755322914, 360583549747723361, 360583550302393833, 360583550857103342, 360583551355457270, 360583551355777812, 360583550210945179, 360583548241365683]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582519920118792, 360582523494698031⟩, ⟨24894242699604346, 24953707057807440⟩, true⟩

def words08 : List Nat := [360583546271874343, 360583545671703143, 360583545742775186, 360583545813906667, 360583545814204246, 360583544189450549, 360583541870432446, 360583540306692364, 360583538742982827, 360583538285550321]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597109031219236, 360597112608858267⟩, ⟨(-333969305288727817), (-333909765675303691)⟩, true⟩

def words09 : List Nat := [360583538244574310, 360583536931231327, 360583535956298953, 360583537117150649, 360583537847883282, 360583538578612408, 360583538578901179, 360583538488727990, 360583539040781872, 360583539592896506]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk245B
