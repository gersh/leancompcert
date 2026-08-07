import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk701

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494669797024682, 362494742732817525⟩, ⟨(-662452669511807883), (-658999678641714693)⟩, true⟩

def state01 : KState := ⟨⟨362471712732035405, 362471785689484425⟩, ⟨946901779760272673, 950356288837937999⟩, true⟩

def words00 : List Nat := [371285342151082315, 371285342153482733, 371285342017860375, 371285341989331395, 371285341959620379, 371285341938807325, 371285341646477660, 371285341355485559, 371285341063547508, 371285340906840551]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362468163234846312, 362468236213947926⟩, ⟨1195856561382848750, 1199312588635105822⟩, true⟩

def words01 : List Nat := [371285340724769096, 371285340737093457, 371285340749084032, 371285340751500991, 371285340580400977, 371285340445062522, 371285340373280868, 371285340375681720, 371285340171477016, 371285339930271873]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486808176983104, 362486881177592911⟩, ⟨(-111552603996357222), (-108095068482016018)⟩, true⟩

def words02 : List Nat := [371285339687983181, 371285339649662879, 371285339665013323, 371285339775919307, 371285339803064433, 371285339805507598, 371285339664494603, 371285339668998635, 371285339822355452, 371285339846819330]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479710955454010, 362479783977929754⟩, ⟨386204158426826627, 389663227511201927⟩, true⟩

def words03 : List Nat := [371285339849798724, 371285339853567379, 371285339910149664, 371285339912795962, 371285339867609127, 371285339859256285, 371285339850070489, 371285339841087733, 371285339560660626, 371285339484452583]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468818858544283, 362468891902416522⟩, ⟨1150282777214744660, 1153743347156977008⟩, true⟩

def words04 : List Nat := [371285339530509361, 371285339532917764, 371285339449993936, 371285339351327280, 371285339251708607, 371285339214968993, 371285339076891123, 371285338960504005, 371285338843312750, 371285338707080200]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489639823835855, 362489712889433619⟩, ⟨(-310430972491916583), (-306968878393434851)⟩, true⟩

def words05 : List Nat := [371285338474263314, 371285338322029756, 371285338170997775, 371285338173441957, 371285338008495115, 371285337811919878, 371285337618014371, 371285337620679461, 371285337617625991, 371285337682717731]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471312126226182, 362471385213514012⟩, ⟨975501403799111793, 978965019785320937⟩, true⟩

def words06 : List Nat := [371285337715140348, 371285337717542940, 371285337479256610, 371285337444947972, 371285337434125032, 371285337436527697, 371285337192528695, 371285336942228630, 371285336690900946, 371285336546274242]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463535960867357, 362463609069769342⟩, ⟨1521258438038633314, 1524723570796642496⟩, true⟩

def words07 : List Nat := [371285336349085492, 371285336324057269, 371285336298260661, 371285336263005228, 371285336033219180, 371285335810753114, 371285335587003663, 371285335566669273, 371285335275350574, 371285334968469779]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473619638621859, 362473692769037459⟩, ⟨813630516307065178, 817097159002989840⟩, true⟩

def words08 : List Nat := [371285334660530186, 371285334556307462, 371285334397044355, 371285334420537568, 371285334422397102, 371285334413295644, 371285334193176222, 371285334108100461, 371285334021836947, 371285333988000317]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470948460735810, 362471021613103816⟩, ⟨1001132536614276117, 1004600720253470557⟩, true⟩

def words09 : List Nat := [371285333823975475, 371285333622375725, 371285333419775326, 371285333347566225, 371285333172816706, 371285333038834383, 371285332904016909, 371285332770251586, 371285332365483217, 371285332164674379]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk701
