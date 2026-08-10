import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk962A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk962B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk962A

def state06 : KState := ⟨⟨362498035697577456, 362498176639673253⟩, ⟨(-1250738403076619589), (-1241578472856665809)⟩, true⟩

def words05 : List Nat := [371285277910602568, 371285277956525486, 371285278092492090, 371285278147022060, 371285278180679349, 371285278215405154, 371285278293435856, 371285278323097290, 371285278459380758, 371285278597134150]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489621327597340, 362489762300138123⟩, ⟨(-440775646954529529), (-431612785944569475)⟩, true⟩

def words06 : List Nat := [371285278714195387, 371285278717571763, 371285278769142205, 371285278851987020, 371285278953318692, 371285278956695324, 371285278926033719, 371285278896071873, 371285278939207210, 371285278989629823]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484795521712771, 362484936524734525⟩, ⟨23820406635760882, 32986202201052280⟩, true⟩

def words07 : List Nat := [371285279056682881, 371285279125133127, 371285279186443839, 371285279189822475, 371285279126271734, 371285279097508553, 371285279122773757, 371285279128942575, 371285279131466353, 371285279131737029]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494146905883933, 362494287939113133⟩, ⟨(-876559394560550584), (-867390690469775376)⟩, true⟩

def words08 : List Nat := [371285279234925631, 371285279289550905, 371285279397703876, 371285279507184022, 371285279588491126, 371285279591870875, 371285279605352160, 371285279663543226, 371285279827916420, 371285279924963631]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362495326268874821, 362495467332895865⟩, ⟨(-990092185327431131), (-980920516136381101)⟩, true⟩

def words09 : List Nat := [371285280018580854, 371285280113342856, 371285280314678165, 371285280478880669, 371285280674088641, 371285280870617686, 371285281065570122, 371285281130089033, 371285281238194622, 371285281348159088]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk962B
