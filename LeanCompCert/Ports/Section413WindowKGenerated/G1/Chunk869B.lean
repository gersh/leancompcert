import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk869A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk869B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk869A

def state06 : KState := ⟨⟨362498739131708557, 362498853256259174⟩, ⟨(-1194332565681231166), (-1187631668122449886)⟩, true⟩

def words05 : List Nat := [371285195489765792, 371285195534107147, 371285195692530251, 371285195742196806, 371285195747827303, 371285195754348514, 371285195847504882, 371285195875818666, 371285196034923992, 371285196195414400]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489633661354759, 362489747813228337⟩, ⟨(-402553108741196031), (-395849835037023655)⟩, true⟩

def words06 : List Nat := [371285196312096616, 371285196315122361, 371285196259867990, 371285196267957499, 371285196315072716, 371285196318120346, 371285196267277223, 371285196216437581, 371285196242149497, 371285196297952705]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474287220787039, 362474401399864604⟩, ⟨932250586299720004, 938956226072354508⟩, true⟩

def words07 : List Nat := [371285196451342664, 371285196605940885, 371285196753696048, 371285196756722501, 371285196728231809, 371285196704279227, 371285196719009669, 371285196722036296, 371285196602531614, 371285196481792316]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481764648464424, 362481878854667205⟩, ⟨281900530256408737, 288608529518561251⟩, true⟩

def words08 : List Nat := [371285196367670197, 371285196371071440, 371285196409670010, 371285196475147937, 371285196518557776, 371285196521592136, 371285196487150120, 371285196524053495, 371285196572300161, 371285196575434174]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479862341604641, 362479976575421199⟩, ⟨447429447205600396, 454139848725125638⟩, true⟩

def words09 : List Nat := [371285196539558332, 371285196501456211, 371285196552660872, 371285196583249738, 371285196640738961, 371285196699432141, 371285196751275566, 371285196754303128, 371285196629896276, 371285196573682408]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk869B
