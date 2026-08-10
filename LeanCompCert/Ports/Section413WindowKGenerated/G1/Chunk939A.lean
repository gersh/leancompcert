import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk939A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk939A
