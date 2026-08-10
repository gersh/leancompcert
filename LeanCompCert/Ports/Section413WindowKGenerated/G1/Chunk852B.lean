import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk852A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk852B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk852A

def state06 : KState := ⟨⟨362492399953751535, 362492509493097033⟩, ⟨(-621447773501121462), (-615141722136316972)⟩, true⟩

def words05 : List Nat := [371285293843307364, 371285293967668624, 371285294127499726, 371285294236756972, 371285294344069499, 371285294452534990, 371285294560293496, 371285294563256982, 371285294597038088, 371285294685363881]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473592471896686, 362473702037604308⟩, ⟨982177242586166669, 988485541725092733⟩, true⟩

def words06 : List Nat := [371285294811039823, 371285294814002725, 371285294772870789, 371285294723190629, 371285294672337119, 371285294664872160, 371285294588394264, 371285294545413930, 371285294501461555, 371285294456294646]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498013586444045, 362498123178981451⟩, ⟨(-1100328444307633523), (-1094017857266796229)⟩, true⟩

def words07 : List Nat := [371285294322356265, 371285294310234054, 371285294407533746, 371285294410548441, 371285294409801401, 371285294386153547, 371285294453313454, 371285294483549452, 371285294635989332, 371285294789806057]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474785217705365, 362474894836995272⟩, ⟨880671545996495823, 886984414627563253⟩, true⟩

def words08 : List Nat := [371285294922700643, 371285294925664003, 371285294893301776, 371285294915078127, 371285294960277594, 371285294963241053, 371285294825344544, 371285294688430154, 371285294550237050, 371285294466666131]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468247949764812, 362468357595691796⟩, ⟨1438307880870489837, 1444623021517135741⟩, true⟩

def words09 : List Nat := [371285294346749556, 371285294314726833, 371285294281764594, 371285294248355221, 371285294090718967, 371285293941675516, 371285293791058231, 371285293778748097, 371285293582509054, 371285293387268785]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk852B
