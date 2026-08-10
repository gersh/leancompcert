import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk792A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489538057817936, 362489632044780421⟩, ⟨(-356114849407775378), (-351088298589131218)⟩, true⟩

def state01 : KState := ⟨⟨362483303495896517, 362483397507172013⟩, ⟨137710859685377959, 142739336223457543⟩, true⟩

def words00 : List Nat := [371285199384773297, 371285199398264863, 371285199400315187, 371285199394160880, 371285199387888968, 371285199390904875, 371285199393382658, 371285199467269661, 371285199541155845, 371285199543988368]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489363068579416, 362489457104597303⟩, ⟨(-342299486394353976), (-337269049889580452)⟩, true⟩

def words01 : List Nat := [371285199551735879, 371285199583667545, 371285199763596958, 371285199766333050, 371285199734213869, 371285199677038980, 371285199682769379, 371285199685816162, 371285199729034875, 371285199785832209]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496218487230077, 362496312547921656⟩, ⟨(-885450261872464911), (-880417870590054225)⟩, true⟩

def words02 : List Nat := [371285199841640250, 371285199844408433, 371285199903041350, 371285200003829038, 371285200150347272, 371285200165365268, 371285200179207342, 371285200193932268, 371285200366696219, 371285200510075484]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477054709875592, 362477148795279654⟩, ⟨633058446822328863, 638092796196783255⟩, true⟩

def words03 : List Nat := [371285200811307230, 371285201113685256, 371285201361088976, 371285201414166366, 371285201466085833, 371285201519349106, 371285201641290166, 371285201644027293, 371285201553974635, 371285201455504248]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480486996233154, 362480581106128384⟩, ⟨361144000055214017, 366180290233781531⟩, true⟩

def words04 : List Nat := [371285201413214754, 371285201416232194, 371285201549300333, 371285201690987520, 371285201801828263, 371285201804565693, 371285201703018245, 371285201669029704, 371285201674776465, 371285201677613984]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk792A
