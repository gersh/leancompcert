import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk722A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk722B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk722A

def state06 : KState := ⟨⟨362501428974688358, 362501506657923449⟩, ⟨(-1177708764914619589), (-1173917822804164139)⟩, true⟩

def words05 : List Nat := [371285259790739350, 371285259824136977, 371285260047591150, 371285260161667871, 371285260244170281, 371285260327478143, 371285260551020754, 371285260679640126, 371285260906160286, 371285261133742990]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491012460538237, 362491090166200041⟩, ⟨(-425035337456907406), (-421242774680063988)⟩, true⟩

def words06 : List Nat := [371285261319078746, 371285261321558612, 371285261347360765, 371285261446163295, 371285261572936053, 371285261575419644, 371285261496281007, 371285261410682204, 371285261426993418, 371285261510519616]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483108847133857, 362483186575118126⟩, ⟨146256129905973568, 150050306042359764⟩, true⟩

def words07 : List Nat := [371285261784100931, 371285262058716508, 371285262332996979, 371285262352859278, 371285262365547773, 371285262379408368, 371285262583219788, 371285262585700556, 371285262559871989, 371285262533973167]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484395728949074, 362484473479169305⟩, ⟨53280967224228837, 57076750689534995⟩, true⟩

def words08 : List Nat := [371285262577161012, 371285262581858288, 371285262703857463, 371285262826846170, 371285262917806919, 371285262920288521, 371285262852598916, 371285262916528554, 371285263029107683, 371285263031675731]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483769642769661, 362483847415557173⟩, ⟨98547569915348625, 102344984883827487⟩, true⟩

def words09 : List Nat := [371285263022608486, 371285263014945433, 371285263093277419, 371285263096011487, 371285263124442307, 371285263162787284, 371285263186682610, 371285263189165182, 371285262992044279, 371285262975514073]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk722B
