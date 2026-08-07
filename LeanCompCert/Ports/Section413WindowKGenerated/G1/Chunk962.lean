import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk962

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499529965990873, 362499670725695534⟩, ⟨(-1393895359651018946), (-1384752980944218832)⟩, true⟩

def state01 : KState := ⟨⟨362487400416076130, 362487541206279831⟩, ⟨(-227006978914038680), (-217861666041617854)⟩, true⟩

def words00 : List Nat := [371285276485657066, 371285276489031441, 371285276553041241, 371285276621859906, 371285276716088066, 371285276719485393, 371285276717173222, 371285276715699002, 371285276763499232, 371285276790921488]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477460055463603, 362477600875978421⟩, ⟨729461953220618614, 738610182482718710⟩, true⟩

def words01 : List Nat := [371285276924911908, 371285277060244068, 371285277194372204, 371285277200570477, 371285277211784945, 371285277224667123, 371285277290850648, 371285277294225344, 371285277216614923, 371285277140606178]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487966508090441, 362488107358873558⟩, ⟨(-281454096610958226), (-272302954784936988)⟩, true⟩

def words02 : List Nat := [371285277091488771, 371285277095306862, 371285277205771436, 371285277317659436, 371285277410418437, 371285277413809781, 371285277472230611, 371285277545415724, 371285277645779423, 371285277678679183]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483344385416248, 362483485266977146⟩, ⟨163401491489460727, 172555595216961321⟩, true⟩

def words03 : List Nat := [371285277710175314, 371285277742847312, 371285277882235390, 371285277973967113, 371285278089187011, 371285278205727411, 371285278299818667, 371285278303194236, 371285278253065232, 371285278238664771]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481522598440991, 362481663510081376⟩, ⟨338728412354261007, 347885411087880803⟩, true⟩

def words04 : List Nat := [371285278301108630, 371285278304484305, 371285278241867649, 371285278159432418, 371285278075735460, 371285278025855382, 371285277920454083, 371285277915524153, 371285277909422206, 371285277903962809]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk962
