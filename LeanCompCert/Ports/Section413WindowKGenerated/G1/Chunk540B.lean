import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk540A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk540B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk540A

def state06 : KState := ⟨⟨362489246610032429, 362489289105085866⟩, ⟨(-234928084743357717), (-233376152210619845)⟩, true⟩

def words05 : List Nat := [371284971755731735, 371284971615299453, 371284971652187019, 371284971770125088, 371284971955747481, 371284972142072113, 371284972297889883, 371284972299704934, 371284972118904776, 371284972200992146]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462748201638972, 362462790712871368⟩, ⟨1197713893532186718, 1199266700784889912⟩, true⟩

def words06 : List Nat := [371284972424504819, 371284972426320053, 371284972194197022, 371284971961948662, 371284971728998012, 371284971509814646, 371284971118918465, 371284970956770804, 371284970793999895, 371284970603768074]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485295102121715, 362485337629790290⟩, ⟨(-21487372382808566), (-19933676344570962)⟩, true⟩

def words07 : List Nat := [371284970194800744, 371284970099638248, 371284970150510897, 371284970152330420, 371284969946425975, 371284969651741693, 371284969356337209, 371284969276398352, 371284969031628428, 371284969040519667]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362465417451236105, 362465459995298781⟩, ⟨1053611075200697908, 1055165657917879026⟩, true⟩

def words08 : List Nat := [371284969046724782, 371284969048572167, 371284968832210809, 371284968896279030, 371284969019858074, 371284969021674071, 371284968690011740, 371284968275243204, 371284967859757586, 371284967587421501]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472808668666897, 362472851229079772⟩, ⟨653860540545953758, 655416007726125550⟩, true⟩

def words09 : List Nat := [371284967228009873, 371284967210654776, 371284967192714113, 371284967182179336, 371284966898104362, 371284966693514805, 371284966569596307, 371284966571424983, 371284966349473337, 371284966127558998]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk540B
