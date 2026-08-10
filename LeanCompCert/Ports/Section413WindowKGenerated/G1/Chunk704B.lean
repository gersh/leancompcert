import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk704A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk704B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk704A

def state06 : KState := ⟨⟨362491623891317064, 362491697607590246⟩, ⟨(-453643604077071027), (-450135760877339657)⟩, true⟩

def words05 : List Nat := [371285309557648231, 371285309530403706, 371285309641967898, 371285309644380653, 371285309518059971, 371285309309964027, 371285309100870615, 371285309093873352, 371285309075782363, 371285309169150864]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483723169085021, 362483796907177030⟩, ⟨103069915082592539, 106579295745955143⟩, true⟩

def words06 : List Nat := [371285309261325695, 371285309263781686, 371285309285654697, 371285309382571852, 371285309494710938, 371285309497140544, 371285309428422377, 371285309362394358, 371285309311030670, 371285309313814549]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467367826825938, 362467441586666951⟩, ⟨1255782763311787969, 1259293676739161385⟩, true⟩

def words07 : List Nat := [371285309421200349, 371285309551047886, 371285309679173263, 371285309681586802, 371285309564305940, 371285309510932325, 371285309462063667, 371285309464477436, 371285309227855531, 371285308977086066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488631387131029, 362488705168616427⟩, ⟨(-242978746296200063), (-239466307264885841)⟩, true⟩

def words08 : List Nat := [371285308725216729, 371285308675338650, 371285308543019960, 371285308495850919, 371285308447954075, 371285308351929830, 371285308062849645, 371285307976015986, 371285307998990571, 371285308049732245]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476928568954569, 362477002372397883⟩, ⟨582087048344775222, 585601035301525218⟩, true⟩

def words09 : List Nat := [371285308100067681, 371285308151195222, 371285308385163683, 371285308532895488, 371285308703224302, 371285308874504965, 371285309003058439, 371285309005473288, 371285308884916259, 371285308770061735]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk704B
