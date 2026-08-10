import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk741A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk741B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk741A

def state06 : KState := ⟨⟨362477583772300709, 362477665760297654⟩, ⟨559540740974194091, 563646854048102563⟩, true⟩

def words05 : List Nat := [371285267707681762, 371285267465632105, 371285267222510615, 371285267116670621, 371285266936369968, 371285266812670205, 371285266688139904, 371285266557941799, 371285266275608666, 371285266176344689]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474584856386704, 362474666867058838⟩, ⟨781999100085856735, 786106894870969563⟩, true⟩

def words06 : List Nat := [371285266154667770, 371285266157234839, 371285266075052284, 371285265977429105, 371285265878894940, 371285265778215562, 371285265602423242, 371285265607224456, 371285265609151464, 371285265584800122]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482916989952684, 362482999023698955⟩, ⟨163956717409255522, 168066223718305510⟩, true⟩

def words07 : List Nat := [371285265443638771, 371285265419419161, 371285265456620742, 371285265459171054, 371285265281770504, 371285265064439050, 371285264846032252, 371285264810240909, 371285264705535661, 371285264677833740]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480904401255934, 362480986457992361⟩, ⟨313212265159390945, 317323476997359301⟩, true⟩

def words08 : List Nat := [371285264649198062, 371285264621784920, 371285264396481747, 371285264325485777, 371285264253187736, 371285264212501349, 371285264021929890, 371285263831476208, 371285263640005140, 371285263631155825]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468046021725086, 362468128101491860⟩, ⟨1267266356412003273, 1271379276985483507⟩, true⟩

def words09 : List Nat := [371285263636418638, 371285263700394126, 371285263726695787, 371285263729246625, 371285263513403983, 371285263299211484, 371285263083698500, 371285263050413002, 371285262821077772, 371285262593095438]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk741B
