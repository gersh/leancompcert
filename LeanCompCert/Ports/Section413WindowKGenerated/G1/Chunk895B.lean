import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk895A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk895B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk895A

def state06 : KState := ⟨⟨362467981805020004, 362468103131401075⟩, ⟨1518637691768260411, 1525974272915631669⟩, true⟩

def words05 : List Nat := [371285142778626083, 371285142746907141, 371285142714089510, 371285142681893795, 371285142482614315, 371285142322878619, 371285142161560363, 371285142076742905, 371285141887483896, 371285141700772621]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488500777343209, 362488622131694488⟩, ⟨(-319113527165642384), (-311774440866043430)⟩, true⟩

def words06 : List Nat := [371285141512645328, 371285141450445758, 371285141376444412, 371285141404031376, 371285141406490906, 371285141401536352, 371285141266553656, 371285141257836192, 371285141337544163, 371285141379655703]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476505174941969, 362476626557722809⟩, ⟨755423977536038165, 762765610420230007⟩, true⟩

def words07 : List Nat := [371285141421898574, 371285141465227130, 371285141538566213, 371285141551064135, 371285141599890880, 371285141649939133, 371285141685861387, 371285141688985825, 371285141558635830, 371285141467417163]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472740943578878, 362472862354215705⟩, ⟨1092642515843413709, 1099986644207116141⟩, true⟩

def words08 : List Nat := [371285141374485157, 371285141375838495, 371285141233044083, 371285141089828241, 371285140945362801, 371285140798231534, 371285140608192773, 371285140526294005, 371285140443369697, 371285140361183080]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487865290354009, 362487986729302087⟩, ⟨(-262438710844985301), (-255092045937495463)⟩, true⟩

def words09 : List Nat := [371285140226256961, 371285140217476817, 371285140246143049, 371285140249267997, 371285140124776154, 371285139967100780, 371285139808168734, 371285139775041401, 371285139716236883, 371285139751635125]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk895B
