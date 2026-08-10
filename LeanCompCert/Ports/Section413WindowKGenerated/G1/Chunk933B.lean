import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk933A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk933B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk933A

def state06 : KState := ⟨⟨362485306450907024, 362485438715707537⟩, ⟨(-35794896202910666), (-27457729951864454)⟩, true⟩

def words05 : List Nat := [371285143852859500, 371285143963051918, 371285144129700417, 371285144240562650, 371285144385030095, 371285144530717102, 371285144641583046, 371285144644850101, 371285144605680128, 371285144612924235]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483598886770108, 362483731180680910⟩, ⟨123641197948466658, 131981082084981128⟩, true⟩

def words06 : List Nat := [371285144719580871, 371285144722848007, 371285144676793241, 371285144631476403, 371285144584928663, 371285144566522006, 371285144582661694, 371285144644583050, 371285144705006218, 371285144708388793]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492174630502151, 362492306953948163⟩, ⟨(-677104191497378127), (-668761549512458173)⟩, true⟩

def words07 : List Nat := [371285144795080518, 371285144898571978, 371285145048167221, 371285145051434740, 371285145048434261, 371285145030611765, 371285145104735002, 371285145149843178, 371285145228779764, 371285145309186248]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482593958702384, 362482726311601210⟩, ⟨217545454165567927, 225890846606198365⟩, true⟩

def words08 : List Nat := [371285145374720001, 371285145377987983, 371285145315355740, 371285145344273073, 371285145397944593, 371285145401213506, 371285145318629057, 371285145214839967, 371285145109750499, 371285145102120604]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485847787137787, 362485980169473668⟩, ⟨(-86310885443326801), (-77962743727503629)⟩, true⟩

def words09 : List Nat := [371285145149708287, 371285145224584994, 371285145299090795, 371285145302417386, 371285145294751058, 371285145311083399, 371285145419927034, 371285145435503054, 371285145446883021, 371285145459527014]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk933B
