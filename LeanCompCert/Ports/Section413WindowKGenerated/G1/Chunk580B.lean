import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk580A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk580B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk580A

def state06 : KState := ⟨⟨362476470568915557, 362476519865495539⟩, ⟨489381669057053255, 491315069420499645⟩, true⟩

def words05 : List Nat := [371284983478532549, 371284983511196693, 371284983516276936, 371284983518236899, 371284983127594920, 371284982769869777, 371284982411123598, 371284982350034107, 371284982204541687, 371284982060972985]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488245852877545, 362488295166984802⟩, ⟨(-194271143313199353), (-192336725225011323)⟩, true⟩

def words06 : List Nat := [371284982067744173, 371284982073721844, 371284982326237391, 371284982579570245, 371284982773924483, 371284982775884969, 371284982668724998, 371284982765258904, 371284983011946664, 371284983071012200]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483904119983964, 362483953452002600⟩, ⟨57932940831967711, 59868399120346211⟩, true⟩

def words07 : List Nat := [371284983125954690, 371284983181610537, 371284983533225724, 371284983738374417, 371284983959389735, 371284984181126160, 371284984395582870, 371284984397543928, 371284984259272947, 371284984243998474]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478179392283164, 362478228741756966⟩, ⟨390495983313141675, 392432455487948915⟩, true⟩

def words08 : List Nat := [371284984491831513, 371284984493792510, 371284984403574700, 371284984304970860, 371284984205627978, 371284984196431741, 371284984183676628, 371284984288152944, 371284984333726473, 371284984335757448]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488045040022643, 362488094407223043⟩, ⟨(-182686385071917999), (-180748883069585007)⟩, true⟩

def words09 : List Nat := [371284984255660978, 371284984292842544, 371284984421719902, 371284984423682796, 371284984219687467, 371284983966922011, 371284983713349546, 371284983596882838, 371284983408731680, 371284983464501411]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk580B
