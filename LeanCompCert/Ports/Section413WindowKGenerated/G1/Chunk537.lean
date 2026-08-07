import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk537

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486919370149184, 362486961278600906⟩, ⟨(-106537807625148485), (-105017481394634319)⟩, true⟩

def state01 : KState := ⟨⟨362484804191424993, 362484846115927108⟩, ⟨7099921028164070, 8621109247236640⟩, true⟩

def words00 : List Nat := [371285006035541066, 371285006079998121, 371285006101391541, 371285006123418359, 371285006190438842, 371285006192424997, 371285006265401998, 371285006446225723, 371285006626241364, 371285006628108215]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503133193298353, 362503175134144178⟩, ⟨(-977514661261111257), (-975992595139874309)⟩, true⟩

def words01 : List Nat := [371285006767016814, 371285006909864808, 371285007160213533, 371285007162016625, 371285006991607465, 371285006765385099, 371285006656507412, 371285006658528633, 371285006989968712, 371285007330210151]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476393535549071, 362476435492672040⟩, ⟨459023690870916892, 460546631481774580⟩, true⟩

def words02 : List Nat := [371285007648622455, 371285007650425740, 371285007653557145, 371285007802187187, 371285007962623731, 371285007964427069, 371285007663378278, 371285007362827743, 371285007061533311, 371285006991489866]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362455023366610387, 362455065339962790⟩, ⟨1607468686883628051, 1608992499586495163⟩, true⟩

def words03 : List Nat := [371285007019671759, 371285007208127219, 371285007395834891, 371285007397638725, 371285007176621728, 371285006969851775, 371285006762144749, 371285006694509132, 371285006209566780, 371285005654432208]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487543531006645, 362487585520506763⟩, ⟨(-140282591681685415), (-138757911118017537)⟩, true⟩

def words04 : List Nat := [371285005098534114, 371285004834787689, 371285004448823381, 371285004363343154, 371285004277281942, 371285004135440043, 371285003800126878, 371285003766227327, 371285003976104078, 371285004026002140]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479605948036638, 362479647954021750⟩, ⟨286405257606863002, 287930824317311966⟩, true⟩

def words05 : List Nat := [371285004027356698, 371285004023619311, 371285004158489833, 371285004175614854, 371285004253793065, 371285004332636194, 371285004349699335, 371285004351503597, 371285003907455490, 371285003810128843]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466707177889640, 362466749199934940⟩, ⟨979925100709621351, 981451530899026601⟩, true⟩

def words06 : List Nat := [371285003878835875, 371285003880640208, 371285003588194198, 371285003296325562, 371285003003794182, 371285002818181951, 371285002498530168, 371285002323124526, 371285002147077964, 371285001971571523]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500308512347947, 362500350550673706⟩, ⟨(-826962912137546819), (-825435606462717077)⟩, true⟩

def words07 : List Nat := [371285001633345747, 371285001512384467, 371285001612802666, 371285001614641447, 371285001614778014, 371285001554006995, 371285001775068437, 371285001887052755, 371285002173683143, 371285002461079561]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481054476106330, 362481096530746017⟩, ⟨208557152411631892, 210085335530651124⟩, true⟩

def words08 : List Nat := [371285002707662883, 371285002709467972, 371285002625298130, 371285002757422038, 371285002966411516, 371285002968216689, 371285002716812124, 371285002466108034, 371285002214659777, 371285002188591912]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471248902259241, 362471290973150754⟩, ⟨736144069389766687, 737673126778105117⟩, true⟩

def words09 : List Nat := [371285002389760016, 371285002664285693, 371285002929464344, 371285002931278562, 371285002865714284, 371285002781712633, 371285002856610188, 371285002858417025, 371285002622375961, 371285002369559269]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk537
