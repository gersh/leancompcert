import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk576A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk576B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk576A

def state06 : KState := ⟨⟨362477027854391876, 362477076447405555⟩, ⟨453457760238101215, 455350452004902603⟩, true⟩

def words05 : List Nat := [371284973638304852, 371284973538359789, 371284973636527128, 371284973686771481, 371284973792282073, 371284973898543904, 371284974002896339, 371284974004841799, 371284973745559885, 371284973610985245]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476687769124299, 362476736379476057⟩, ⟨473085309200756288, 474979000769826746⟩, true⟩

def words06 : List Nat := [371284973540217150, 371284973542175727, 371284973339718322, 371284973113249078, 371284972886012425, 371284972726496417, 371284972484106380, 371284972514789222, 371284972531454447, 371284972533468945]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490770301291898, 362490818929269196⟩, ⟨(-339162373088058953), (-337267664967810505)⟩, true⟩

def words07 : List Nat := [371284972499509786, 371284972609408563, 371284972743797882, 371284972745743823, 371284972479493708, 371284972165715127, 371284971851174329, 371284971803415561, 371284971706752707, 371284971810374451]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469466072456653, 362469514717999028⟩, ⟨889714834017263010, 891610555379260700⟩, true⟩

def words08 : List Nat := [371284971880522478, 371284971882468687, 371284971586244102, 371284971524325094, 371284971476267457, 371284971478213881, 371284971093895886, 371284970602326474, 371284970109965839, 371284969919166982]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474127833095285, 362474176496147053⟩, ⟨620819627888999847, 622716359458860165⟩, true⟩

def words09 : List Nat := [371284969652592497, 371284969636629597, 371284969620028509, 371284969602746796, 371284969410174716, 371284969232470236, 371284969174222739, 371284969176174872, 371284968992277412, 371284968807402840]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk576B
