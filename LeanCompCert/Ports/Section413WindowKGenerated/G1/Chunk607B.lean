import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk607A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk607B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk607A

def state06 : KState := ⟨⟨362481214743865561, 362481268927134416⟩, ⟨240443757499104536, 242667530268995912⟩, true⟩

def words05 : List Nat := [371285262295124342, 371285262618029918, 371285262843706311, 371285262845765209, 371285262757360696, 371285262717266060, 371285262904759695, 371285262906823306, 371285262860314370, 371285262796954512]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362501202147892247, 362501256349586697⟩, ⟨(-974010178943251131), (-971785286541714339)⟩, true⟩

def words06 : List Nat := [371285262938033459, 371285263078296721, 371285263488804466, 371285263900132187, 371285264269466112, 371285264348784999, 371285264538346036, 371285264728996087, 371285265146426229, 371285265411696228]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503605379926210, 362503659600337654⟩, ⟨(-1120043409402982290), (-1117817379472665478)⟩, true⟩

def words07 : List Nat := [371285265665062303, 371285265919095808, 371285266443355722, 371285266868846427, 371285267265072688, 371285267662070364, 371285268056164829, 371285268089817361, 371285268393805492, 371285268698913317]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488543909603805, 362488598148387484⟩, ⟨(-204546999848991962), (-202319853159191800)⟩, true⟩

def words08 : List Nat := [371285269079031595, 371285269098875973, 371285269117431439, 371285269136710345, 371285269236632697, 371285269244250186, 371285269492474975, 371285269741559684, 371285269969694685, 371285270026574071]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505571429693581, 362505625687099100⟩, ⟨(-1239736895265994224), (-1237508616463129050)⟩, true⟩

def words09 : List Nat := [371285270230016294, 371285270434541640, 371285270908849519, 371285271061435851, 371285271157588736, 371285271254318060, 371285271488328329, 371285271588440019, 371285271924608484, 371285272261720190]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk607B
