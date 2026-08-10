import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk858A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk858B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk858A

def state06 : KState := ⟨⟨360587675748500493, 360587724029370381⟩, ⟨(-466620460959946863), (-463820995082408637)⟩, true⟩

def words05 : List Nat := [360582320665693865, 360582320777536745, 360582321024671987, 360582321359325993, 360582321562967233, 360582321766780054, 360582321902473660, 360582321903707973, 360582321966509065, 360582322030848557]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588668537144993, 360588716829656962⟩, ⟨(-551858755950784259), (-549058290425988299)⟩, true⟩

def words06 : List Nat := [360582322154610606, 360582322282358035, 360582322341989986, 360582322401755328, 360582322402793229, 360582322476119001, 360582322610479994, 360582322745071840, 360582322764206266, 360582322839946513]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597444691267141, 360597492995430289⟩, ⟨(-1305531636063333225), (-1302730169994454733)⟩, true⟩

def words07 : List Nat := [360582323001286089, 360582323162984262, 360582323426505973, 360582323554591760, 360582323563009061, 360582323571542344, 360582323572547542, 360582323624970691, 360582323802603086, 360582323980514366]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586588040200415, 360586636356133415⟩, ⟨(-373227538699917541), (-370425061777655829)⟩, true⟩

def words08 : List Nat := [360582324090321567, 360582324138275144, 360582324182532836, 360582324227138519, 360582324228171798, 360582324219692580, 360582324075461403, 360582323862393221, 360582323649084694, 360582323621833225]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554362270294022, 360554410597848936⟩, ⟨2394855807883527736, 2397659283070963536⟩, true⟩

def words09 : List Nat := [360582323713490917, 360582323805378576, 360582323829238731, 360582323830473747, 360582323760293348, 360582323624164902, 360582323487681817, 360582323347887874, 360582323136680818, 360582322813018564]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk858B
