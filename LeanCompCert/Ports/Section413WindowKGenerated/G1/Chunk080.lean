import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk080

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362607936206906368, 362607936995584247⟩, ⟨(-987579650660323564), (-987575378161835628)⟩, true⟩

def state01 : KState := ⟨⟨362462494374936741, 362462495165691642⟩, ⟨176131767901704453, 176136057026834591⟩, true⟩

def words00 : List Nat := [371284517602207116, 371284517602436742, 371284512685368076, 371284516408209031, 371284524893318889, 371284524893548698, 371284512664479083, 371284498159150787, 371284484685655756, 371284484685919712]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362396906290292054, 362396907083112570⟩, ⟨702371059742529049, 702375365424108105⟩, true⟩

def words01 : List Nat := [371284494719723653, 371284507495344388, 371284520161904973, 371284520162134934, 371284512149716260, 371284504240982649, 371284503929807801, 371284503930038332, 371284495979904392, 371284485058851237]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362424269693419214, 362424270488304038⟩, ⟨483272513392646182, 483276835640585450⟩, true⟩

def words02 : List Nat := [371284474140422933, 371284473298142226, 371284473717226609, 371284480471612591, 371284484719410483, 371284484719640826, 371284468352773982, 371284462503654774, 371284456655877578, 371284454403078707]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362457432580887000, 362457433377873752⟩, ⟨216956465315253419, 216960804452310259⟩, true⟩

def words03 : List Nat := [371284446909301094, 371284439334840967, 371284435410806635, 371284435411061595, 371284436132013776, 371284438874060672, 371284440664283289, 371284440664514080, 371284421909052640, 371284418552556876]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362299687414887836, 362299688213935461⟩, ⟨1485670106473108526, 1485674462190319282⟩, true⟩

def words04 : List Nat := [371284415196767947, 371284414201846051, 371284392677592926, 371284368034117762, 371284343396683652, 371284323532753638, 371284296091995539, 371284278758615387, 371284261429462197, 371284244047747924]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362463243296874397, 362463244098008049⟩, ⟨168245227274558237, 168249599794832591⟩, true⟩

def words05 : List Nat := [371284221124562390, 371284210295070423, 371284203978128808, 371284203978359993, 371284188023675068, 371284169629840112, 371284151240478205, 371284139230357890, 371284121328149649, 371284118738181106]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362392954935593451, 362392955738816282⟩, ⟨734647993655361118, 734652383025051610⟩, true⟩

def words06 : List Nat := [371284116148769988, 371284113530476042, 371284094850178752, 371284083943840398, 371284073040083117, 371284066904672340, 371284044048659391, 371284021181600646, 371283998320118606, 371283990730517032]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362323864375288866, 362323865180604434⟩, ⟨1292750541480937948, 1292754947749805000⟩, true⟩

def words07 : List Nat := [371283979451407075, 371283974557100891, 371283969663930487, 371283963537167602, 371283943927880644, 371283925168999721, 371283906414647629, 371283899216734867, 371283879408308865, 371283859604830896]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485331445655936, 362485332253047630⟩, ⟨(-12441739865406483), (-12437316810672911)⟩, true⟩

def words08 : List Nat := [371283839806149097, 371283835230169848, 371283823120812776, 371283822635988796, 371283822151219276, 371283816011388600, 371283795528053201, 371283790247459655, 371283794883609446, 371283795073859561]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362456952120407400, 362456952929920475⟩, ⟨217861995040066886, 217866435267174046⟩, true⟩

def words09 : List Nat := [371283795074035346, 371283794562078301, 371283808722866092, 371283817888865999, 371283831804317492, 371283845716425107, 371283859647411931, 371283859647644490, 371283853341445174, 371283850020694201]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk080
