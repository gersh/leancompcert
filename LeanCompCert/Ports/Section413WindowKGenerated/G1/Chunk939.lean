import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk939

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487271299171587, 362487405158157156⟩, ⟨(-220071660632933501), (-211585230163600641)⟩, true⟩

def state01 : KState := ⟨⟨362480415710764860, 362480549599008211⟩, ⟨423739110059505146, 432228287987243614⟩, true⟩

def words00 : List Nat := [371285152017970454, 371285152035963661, 371285152055040375, 371285152075270946, 371285152099236035, 371285152102900216, 371285152113366885, 371285152149859273, 371285152175606232, 371285152179010205]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494179074650245, 362494312992696436⟩, ⟨(-868822180854453246), (-860330203995861268)⟩, true⟩

def words01 : List Nat := [371285152196631927, 371285152265087829, 371285152445125872, 371285152475099853, 371285152485602452, 371285152497076629, 371285152590141581, 371285152644220115, 371285152744022047, 371285152845296006]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485937010043482, 362486070957733317⟩, ⟨(-94707042621088535), (-86212281479025441)⟩, true⟩

def words02 : List Nat := [371285152945044263, 371285152948332769, 371285152977240214, 371285153051204977, 371285153130386032, 371285153133731945, 371285153118753398, 371285153101112826, 371285153118552895, 371285153132079603]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479905955013018, 362480039932344431⟩, ⟨471830487315057471, 480328032837196121⟩, true⟩

def words03 : List Nat := [371285153199754918, 371285153268740491, 371285153312220724, 371285153315510219, 371285153224496792, 371285153169659020, 371285153167589060, 371285153170893931, 371285153119414054, 371285153068738270]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488160527883378, 362488294534589768⟩, ⟨(-303606394016823578), (-295106088855278276)⟩, true⟩

def words04 : List Nat := [371285153075459409, 371285153092566829, 371285153196271813, 371285153301342648, 371285153387589472, 371285153390879145, 371285153338168596, 371285153334162040, 371285153433906553, 371285153470749519]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486157071001423, 362486291107753990⟩, ⟨(-115353721935798480), (-106850593792514084)⟩, true⟩

def words05 : List Nat := [371285153492747316, 371285153515851684, 371285153632524753, 371285153709492257, 371285153790303615, 371285153872335782, 371285153953019790, 371285153956309933, 371285153911244451, 371285153927500561]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482164380538230, 362482298446623636⟩, ⟨259820297980828379, 268326182392172959⟩, true⟩

def words06 : List Nat := [371285153980901806, 371285153984214282, 371285153936460768, 371285153889548865, 371285153841389386, 371285153829035392, 371285153799589290, 371285153844069085, 371285153888384850, 371285153891791160]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497920552812581, 362498054648586920⟩, ⟨(-1220869902898881483), (-1212361228467857663)⟩, true⟩

def words07 : List Nat := [371285153946526101, 371285154033319256, 371285154176071514, 371285154202769484, 371285154205362761, 371285154204624882, 371285154273142488, 371285154300819188, 371285154440316923, 371285154581249184]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488886152412401, 362489020277912119⟩, ⟨(-371763043987308492), (-363251575816760130)⟩, true⟩

def words08 : List Nat := [371285154720711991, 371285154771048700, 371285154933513671, 371285155097758711, 371285155294761065, 371285155341856965, 371285155379882571, 371285155418963860, 371285155484525375, 371285155529416873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481151553688965, 362481285708853522⟩, ⟨355285074046226103, 363799330564311507⟩, true⟩

def words09 : List Nat := [371285155679943278, 371285155831839240, 371285155956867488, 371285155960158683, 371285155934182258, 371285155916010800, 371285155987094599, 371285155990387176, 371285155951922232, 371285155914497824]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk939
