import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk577A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk577B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk577A

def state06 : KState := ⟨⟨362467250591504702, 362467299359860518⟩, ⟨1019055311223170982, 1020958122006271580⟩, true⟩

def words05 : List Nat := [371284975113585513, 371284975427501308, 371284975724033069, 371284975725982077, 371284975698206538, 371284975731263117, 371284975830150792, 371284975832099663, 371284975531430162, 371284975227623785]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476484464775742, 362476533250565535⟩, ⟨485667416000454043, 487571233859309771⟩, true⟩

def words06 : List Nat := [371284974922938195, 371284974713435578, 371284974352921964, 371284974244588243, 371284974135633461, 371284973981002487, 371284973520691482, 371284973313129128, 371284973117577279, 371284973119595470]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485384245589875, 362485433049167435⟩, ⟨(-28513593614306549), (-26608748067597359)⟩, true⟩

def words07 : List Nat := [371284972975000977, 371284972772840996, 371284972665419328, 371284972667567345, 371284972652765528, 371284972692101076, 371284972729430927, 371284972731414413, 371284972528438875, 371284972538825496]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473699771843622, 362473748592759840⟩, ⟨646696644768972577, 648602492234903713⟩, true⟩

def words08 : List Nat := [371284972847836846, 371284972849786610, 371284972799677929, 371284972649259513, 371284972498112180, 371284972344001488, 371284972040198246, 371284972036845619, 371284972032866827, 371284972030936600]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505329522319881, 362505378360932126⟩, ⟨(-1181282272705609205), (-1179375402503433689)⟩, true⟩

def words09 : List Nat := [371284971943491644, 371284972051330685, 371284972457715259, 371284972649005875, 371284972793941449, 371284972939460923, 371284973304642026, 371284973585614956, 371284973939987179, 371284974295215211]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk577B
