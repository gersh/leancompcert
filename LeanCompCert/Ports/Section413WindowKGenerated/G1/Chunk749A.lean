import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk749A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk749A
