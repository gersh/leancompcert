import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk749

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490122920707945, 362490206617339882⟩, ⟨(-376060764866886655), (-371827305911435463)⟩, true⟩

def state01 : KState := ⟨⟨362488572986107248, 362488656705967866⟩, ⟨(-259999209781361337), (-255764010878480949)⟩, true⟩

def words00 : List Nat := [371285242435456800, 371285242438040859, 371285242385822155, 371285242450987676, 371285242555801330, 371285242558392223, 371285242529413739, 371285242439443692, 371285242419055388, 371285242467593282]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 74900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 74900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485073561219033, 362485157304300375⟩, ⟨2213362930772934, 6450301419763686⟩, true⟩

def words01 : List Nat := [371285242641032221, 371285242815549620, 371285242989290489, 371285243015560318, 371285243095455483, 371285243176624003, 371285243388354174, 371285243396442846, 371285243398384313, 371285243400154884]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 74910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 74900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489388122028498, 362489471888204473⟩, ⟨(-321065079861948657), (-316826411005621405)⟩, true⟩

def words02 : List Nat := [371285243419025933, 371285243421866689, 371285243460014229, 371285243569976391, 371285243637230626, 371285243639808659, 371285243469439201, 371285243450834778, 371285243586976242, 371285243646074973]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 74920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 74900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493475561614436, 362493559351244486⟩, ⟨(-627336567722020300), (-623096141333542332)⟩, true⟩

def words03 : List Nat := [371285243704584629, 371285243763972558, 371285244000229074, 371285244164302958, 371285244335462570, 371285244507613183, 371285244679005133, 371285244681583816, 371285244747848064, 371285244861961804]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 74930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 74900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491341776303973, 362491425588923619⟩, ⟨(-467367240366205956), (-463125091017538592)⟩, true⟩

def words04 : List Nat := [371285245152549728, 371285245314277467, 371285245441911824, 371285245570419611, 371285245732063620, 371285245805746197, 371285246036406397, 371285246268088042, 371285246465623359, 371285246550738438]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 74940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 74900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362516894534040383, 362516978370017154⟩, ⟨(-2382680788347918687), (-2378436888266062241)⟩, true⟩

def words05 : List Nat := [371285246797650831, 371285247045948923, 371285247405906788, 371285247607110594, 371285247789021559, 371285247971751714, 371285248279487128, 371285248527847171, 371285248952886737, 371285249379098329]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497202692280513, 362497286551559489⟩, ⟨(-906533658786061282), (-902288011853129540)⟩, true⟩

def words06 : List Nat := [371285249803595588, 371285250023347870, 371285250316606583, 371285250611136255, 371285250893427808, 371285250939381156, 371285250984875711, 371285251031263476, 371285251227575530, 371285251391139419]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481411735774184, 362481495618248465⟩, ⟨277446402880450506, 281693788882790756⟩, true⟩

def words07 : List Nat := [371285251651324279, 371285251912520098, 371285252156215526, 371285252216134955, 371285252329319636, 371285252443834388, 371285252631301898, 371285252633881756, 371285252584506622, 371285252537278644]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479163858200588, 362479247763758479⟩, ⟨446078631066191958, 450327747996653228⟩, true⟩

def words08 : List Nat := [371285252587619864, 371285252600238465, 371285252773359600, 371285252947612381, 371285253092216177, 371285253094796307, 371285253002215671, 371285252951024856, 371285252931750121, 371285252934421190]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487390778889238, 362487474708010066⟩, ⟨(-170916265863335587), (-166665381830820115)⟩, true⟩

def words09 : List Nat := [371285252856305034, 371285252743375054, 371285252645335567, 371285252648181576, 371285252595038118, 371285252589884725, 371285252583910699, 371285252576573037, 371285252499694536, 371285252532547995]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk749
