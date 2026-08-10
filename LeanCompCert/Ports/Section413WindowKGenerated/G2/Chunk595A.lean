import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk595A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588096441656392, 360588118965616557⟩, ⟨(-360689687528248540), (-359784288837878614)⟩, true⟩

def state01 : KState := ⟨⟨360605807656734541, 360605830188544978⟩, ⟨(-1414654099983506425), (-1413748234163581459)⟩, true⟩

def words00 : List Nat := [360582072339992323, 360582072575421277, 360582073031485029, 360582073487693023, 360582073704971338, 360582073705803439, 360582073641634228, 360582073569232783, 360582073705840154, 360582074105902046]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605250918627273, 360605273458355057⟩, ⟨(-1381483676078270487), (-1380577339057727575)⟩, true⟩

def words01 : List Nat := [360582074348876841, 360582074591934814, 360582075117391517, 360582075864102351, 360582076538127785, 360582077212266606, 360582077688350159, 360582077883233878, 360582078273617286, 360582078664264607]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569112723412682, 360569135270986781⟩, ⟨769549162168327395, 770455966242012153⟩, true⟩

def words02 : List Nat := [360582078909469567, 360582078910301921, 360582078874303750, 360582078696203373, 360582078517972608, 360582078268177943, 360582078162965930, 360582078017790588, 360582077872514624, 360582077585218967]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360605001971150384, 360605024526580319⟩, ⟨(-1367166940205358400), (-1366259668436822632)⟩, true⟩

def words03 : List Nat := [360582077368487293, 360582077339089728, 360582077442616702, 360582077523306006, 360582077524095025, 360582077337936383, 360582077151624809, 360582077218764478, 360582077604847268, 360582077991110025]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586297106045828, 360586319669409735⟩, ⟨(-253448879104154916), (-252541134907395346)⟩, true⟩

def words04 : List Nat := [360582078208024713, 360582078431369153, 360582078696228850, 360582078961328099, 360582079153873604, 360582079225099636, 360582079225842248, 360582079118921950, 360582079011857550, 360582078915519668]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk595A
