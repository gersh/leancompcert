import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk895

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478455374484258, 362478576532031252⟩, ⟨580349030681485807, 587670496095195591⟩, true⟩

def state01 : KState := ⟨⟨362474289300171209, 362474410485692907⟩, ⟨953302353710109117, 960626323003934581⟩, true⟩

def words00 : List Nat := [371285142662941005, 371285142671939900, 371285142733842280, 371285142797056076, 371285142842531614, 371285142845653481, 371285142724477262, 371285142652376845, 371285142578734161, 371285142541586148]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487182975791294, 362487304189791321⟩, ⟨(-200884372386180812), (-193557853853672380)⟩, true⟩

def words01 : List Nat := [371285142424023068, 371285142307392959, 371285142194122579, 371285142197595734, 371285142141752093, 371285142125167559, 371285142107493853, 371285142085722420, 371285142011461463, 371285142039526538]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486577826404458, 362486699068233431⟩, ⟨(-146691296208488259), (-139362286284203733)⟩, true⟩

def words02 : List Nat := [371285142190475544, 371285142214874617, 371285142217274323, 371285142209371217, 371285142226634088, 371285142230076754, 371285142295627709, 371285142393102599, 371285142466191949, 371285142486867377]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490482704102088, 362490603974122077⟩, ⟨(-496295943765515975), (-488964409756908705)⟩, true⟩

def words03 : List Nat := [371285142564618382, 371285142643981476, 371285142846373753, 371285142898136025, 371285142927518053, 371285142957916208, 371285143038720652, 371285143058609969, 371285143121725188, 371285143186217577]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480537847619571, 362480659145825356⟩, ⟨394179548731938713, 401513606635917299⟩, true⟩

def words04 : List Nat := [371285143250163303, 371285143253286540, 371285143155360260, 371285143163781593, 371285143208552606, 371285143211675919, 371285143090408728, 371285142966587691, 371285142841525408, 371285142826524808]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk895
