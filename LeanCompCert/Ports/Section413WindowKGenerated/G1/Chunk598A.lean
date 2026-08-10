import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk598A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495629827619247, 362495682246042070⟩, ⟨(-633060770561636152), (-630943385277068344)⟩, true⟩

def state01 : KState := ⟨⟨362504229884883308, 362504282321436737⟩, ⟨(-1147369941835276957), (-1145251472247717619)⟩, true⟩

def words00 : List Nat := [371285131821729857, 371285131975395306, 371285132377813507, 371285132781022611, 371285133143155058, 371285133220874455, 371285133439844679, 371285133659918687, 371285134158963461, 371285134481202538]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502259739287904, 362502312194235676⟩, ⟨(-1029521870806303486), (-1027402300956481816)⟩, true⟩

def words01 : List Nat := [371285134801563037, 371285135122582064, 371285135587393923, 371285135913639168, 371285136256143170, 371285136599403539, 371285136927657079, 371285137006892243, 371285137295380399, 371285137584968755]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496097206560989, 362496149679563387⟩, ⟨(-660787000352988407), (-658666350382200787)⟩, true⟩

def words02 : List Nat := [371285138116905019, 371285138418314038, 371285138669507526, 371285138921381531, 371285139258482764, 371285139494973328, 371285139936184214, 371285140378183943, 371285140712893823, 371285140898991741]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362513973428186417, 362514025919521712⟩, ⟨(-1730413090970370238), (-1728291344053142998)⟩, true⟩

def words03 : List Nat := [371285141232426579, 371285141566938278, 371285142180237989, 371285142421624590, 371285142619883093, 371285142818784489, 371285143257999709, 371285143559091457, 371285144043131289, 371285144528100227]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494751696896277, 362494804206514225⟩, ⟨(-580172607651267975), (-578049766607566897)⟩, true⟩

def words04 : List Nat := [371285144997346367, 371285145094637253, 371285145287425817, 371285145481210594, 371285145757814362, 371285145759842136, 371285145737029918, 371285145713637021, 371285145895586850, 371285146059338613]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk598A
