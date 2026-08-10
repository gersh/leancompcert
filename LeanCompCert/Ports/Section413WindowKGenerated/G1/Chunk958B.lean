import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk958A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk958B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk958A

def state06 : KState := ⟨⟨362488569383266616, 362488709111662850⟩, ⟨(-340299925640007438), (-331256583666192264)⟩, true⟩

def words05 : List Nat := [371285253128109156, 371285253212024991, 371285253290678332, 371285253294062092, 371285253278843575, 371285253286547283, 371285253401445563, 371285253440461875, 371285253479046100, 371285253518839218]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495355639610844, 362495495398065306⟩, ⟨(-990838939634824488), (-981792716123668098)⟩, true⟩

def words06 : List Nat := [371285253656493647, 371285253753990828, 371285253918240291, 371285254083884741, 371285254214547688, 371285254217909231, 371285254270059422, 371285254341064766, 371285254519273507, 371285254629573023]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493178472786381, 362493318261955630⟩, ⟨(-782062254986381252), (-773013086702607998)⟩, true⟩

def words07 : List Nat := [371285254738413836, 371285254848502064, 371285255066048357, 371285255252582133, 371285255447972001, 371285255644626084, 371285255831347018, 371285255873814122, 371285255960221382, 371285256048517070]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486855218464266, 362486995037575291⟩, ⟨(-175729902913989532), (-166677863656380850)⟩, true⟩

def words08 : List Nat := [371285256243804345, 371285256305397931, 371285256368151587, 371285256432008171, 371285256519480638, 371285256569406102, 371285256650774380, 371285256733553534, 371285256814636968, 371285256836246112]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494715884417737, 362494855733902724⟩, ⟨(-929532252444872478), (-920477300473486876)⟩, true⟩

def words09 : List Nat := [371285256965559230, 371285257096578985, 371285257250724292, 371285257260875046, 371285257263500639, 371285257255599433, 371285257302901742, 371285257324272095, 371285257426640274, 371285257530542244]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk958B
