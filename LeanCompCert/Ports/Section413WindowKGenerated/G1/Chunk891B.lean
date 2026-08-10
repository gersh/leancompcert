import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk891A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk891B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk891A

def state06 : KState := ⟨⟨362479392747599258, 362479512951301910⟩, ⟨494978286785698063, 502214545070772843⟩, true⟩

def words05 : List Nat := [371285145523782942, 371285145503540784, 371285145583905401, 371285145643967108, 371285145709439993, 371285145776062278, 371285145842570375, 371285145845678703, 371285145744392044, 371285145685095885]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473018518997894, 362473138750386995⟩, ⟨1063355493134857188, 1070594220088818814⟩, true⟩

def words06 : List Nat := [371285145670980509, 371285145674089139, 371285145571433508, 371285145470385216, 371285145368182030, 371285145278347670, 371285145154375574, 371285145091954646, 371285145028443875, 371285144965707045]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477680192142497, 362477800451634052⟩, ⟨647640561711745292, 654881794701589394⟩, true⟩

def words07 : List Nat := [371285144833175629, 371285144792541174, 371285144758147767, 371285144761256822, 371285144603934009, 371285144416883457, 371285144228557613, 371285144094045401, 371285143901087194, 371285143822285562]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476381643304356, 362476501930864473⟩, ⟨763423498170393601, 770667234458099447⟩, true⟩

def words08 : List Nat := [371285143742291487, 371285143660490773, 371285143473755567, 371285143396314705, 371285143317291391, 371285143277579861, 371285143106884437, 371285142918660836, 371285142729180702, 371285142666759283]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476412680287889, 362476532995864307⟩, ⟨760718080449669501, 767964315655581279⟩, true⟩

def words09 : List Nat := [371285142589839869, 371285142611092847, 371285142629430209, 371285142632598856, 371285142569069479, 371285142545428521, 371285142611742502, 371285142614852664, 371285142554265544, 371285142461286455]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk891B
