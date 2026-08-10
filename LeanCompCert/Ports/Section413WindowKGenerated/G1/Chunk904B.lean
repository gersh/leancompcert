import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk904A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk904B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk904A

def state06 : KState := ⟨⟨362480622711456988, 362480746583901247⟩, ⟨387842463306818583, 395408217841071181⟩, true⟩

def words05 : List Nat := [371285117418198940, 371285117509664984, 371285117577584339, 371285117580813098, 371285117608443615, 371285117639212703, 371285117743287380, 371285117746446806, 371285117712254011, 371285117667450231]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483943298444592, 362484067199191562⟩, ⟨87449101014492345, 95017415954528505⟩, true⟩

def words06 : List Nat := [371285117623800383, 371285117627279851, 371285117615744603, 371285117664037075, 371285117680059688, 371285117683216956, 371285117536117587, 371285117471981175, 371285117460274625, 371285117463543884]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487429108596377, 362487553038134168⟩, ⟨(-227923220022407710), (-220352300238557926)⟩, true⟩

def words07 : List Nat := [371285117454295721, 371285117440874364, 371285117531366006, 371285117589482538, 371285117631071408, 371285117673783149, 371285117717150246, 371285117720314811, 371285117663904609, 371285117694799783]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490782646361703, 362490906604042958⟩, ⟨(-531320253162906077), (-523746786809221191)⟩, true⟩

def words08 : List Nat := [371285117845939783, 371285117918531613, 371285117990169344, 371285118062843691, 371285118171697686, 371285118239993949, 371285118399140754, 371285118559597084, 371285118703913993, 371285118771144557]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497835582843992, 362497959569036913⟩, ⟨(-1169585484555843300), (-1162009438036694822)⟩, true⟩

def words09 : List Nat := [371285118914429191, 371285119059308915, 371285119283849875, 371285119346670279, 371285119388759377, 371285119431914423, 371285119514865575, 371285119538199890, 371285119682220455, 371285119827619286]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk904B
