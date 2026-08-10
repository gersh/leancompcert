import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk681A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk681B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk681A

def state06 : KState := ⟨⟨362483044109732808, 362483112913570560⟩, ⟨156085789163231239, 159253117434365967⟩, true⟩

def words05 : List Nat := [371285448483986182, 371285448620645255, 371285448842794636, 371285448966618178, 371285449139152085, 371285449312568138, 371285449484755982, 371285449487085647, 371285449404985694, 371285449373626816]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479815573582216, 362479884398146930⟩, ⟨376186973196805556, 379355714327894218⟩, true⟩

def words06 : List Nat := [371285449521690817, 371285449524020064, 371285449445084229, 371285449367108181, 371285449288263547, 371285449275956972, 371285449201854383, 371285449221742201, 371285449244112959, 371285449246530793]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498835572258917, 362498904417895628⟩, ⟨(-920504503753909761), (-917334326040036533)⟩, true⟩

def words07 : List Nat := [371285449299824965, 371285449435950924, 371285449661130413, 371285449663460335, 371285449627784680, 371285449549068240, 371285449581342642, 371285449620760027, 371285449819683945, 371285450019660929]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477375389561846, 362477444256194651⟩, ⟨542741613243213367, 545913222580153109⟩, true⟩

def words08 : List Nat := [371285450218945166, 371285450221275562, 371285450274771476, 371285450386118171, 371285450536901613, 371285450539232002, 371285450425208876, 371285450254508485, 371285450082896759, 371285450022767172]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473739038650884, 362473807926291934⟩, ⟨790745669103251768, 793918711098310162⟩, true⟩

def words09 : List Nat := [371285449906950159, 371285449887766713, 371285449867780348, 371285449847997813, 371285449648421393, 371285449470599477, 371285449291600911, 371285449293178888, 371285449131141104, 371285448963111558]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk681B
