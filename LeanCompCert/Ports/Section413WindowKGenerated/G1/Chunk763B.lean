import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk763A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk763B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk763A

def state06 : KState := ⟨⟨362473666591844812, 362473753713181169⟩, ⟨870021207616612567, 874513685870298379⟩, true⟩

def words05 : List Nat := [371285206510532433, 371285206616890284, 371285206722502532, 371285206725133264, 371285206602079358, 371285206532629792, 371285206515836221, 371285206518467393, 371285206370470747, 371285206223472818]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486785372655681, 362486872517582665⟩, ⟨(-131789548139923141), (-127295268387263769)⟩, true⟩

def words06 : List Nat := [371285206075282464, 371285206055052237, 371285205998022339, 371285206007136124, 371285206009191165, 371285205992160194, 371285205745825088, 371285205672250865, 371285205691865210, 371285205716461988]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480671555593151, 362480758724438112⟩, ⟨335160620441573098, 339656726933111540⟩, true⟩

def words07 : List Nat := [371285205740247786, 371285205764898780, 371285205857848545, 371285205866749488, 371285205901101019, 371285205936471748, 371285205938473010, 371285205939966121, 371285205712217917, 371285205657233780]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474557737516593, 362474644929814878⟩, ⟨802164868189593756, 806662766163218308⟩, true⟩

def words08 : List Nat := [371285205651134411, 371285205653766400, 371285205495428349, 371285205314253384, 371285205131964867, 371285205002973218, 371285204804516963, 371285204778393905, 371285204751392323, 371285204725156719]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488216978422226, 362488304194572901⟩, ⟨(-241358523540542386), (-236858803364844204)⟩, true⟩

def words09 : List Nat := [371285204588740058, 371285204524114540, 371285204542434403, 371285204545066641, 371285204403181950, 371285204212840878, 371285204021456719, 371285203989291540, 371285203945458559, 371285203989034167]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk763B
