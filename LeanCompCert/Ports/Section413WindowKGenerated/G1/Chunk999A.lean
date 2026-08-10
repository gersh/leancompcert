import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk999A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483079420242978, 362483231655782529⟩, ⟨202515851157391177, 212783579914956903⟩, true⟩

def state01 : KState := ⟨⟨362485022532445890, 362485174799280336⟩, ⟨8423749377104657, 18694604655292031⟩, true⟩

def words00 : List Nat := [371285361681529548, 371285361695625259, 371285361708668766, 371285361723017653, 371285361742053611, 371285361745925773, 371285361781619204, 371285361852169323, 371285361910091906, 371285361913729894]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492680251805378, 362492832550480174⟩, ⟨(-756731614137065511), (-746457577530991835)⟩, true⟩

def words01 : List Nat := [371285361953608292, 371285361997177378, 371285362083426875, 371285362086940558, 371285362039967617, 371285361978530033, 371285361927297224, 371285361931294244, 371285361994267298, 371285362073027677]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488314006696902, 362488466337023961⟩, ⟨(-320470119333066781), (-310192919866152581)⟩, true⟩

def words02 : List Nat := [371285362148187765, 371285362151702790, 371285362168957953, 371285362230688716, 371285362292474234, 371285362295997916, 371285362255135958, 371285362215444274, 371285362230944277, 371285362266016305]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476054455372751, 362476206817369892⟩, ⟨904730941746814714, 915011306162905908⟩, true⟩

def words03 : List Nat := [371285362365757765, 371285362466953407, 371285362566791503, 371285362570309081, 371285362561735209, 371285362545322548, 371285362577368588, 371285362580883385, 371285362511482783, 371285362423795377]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491281136772611, 362491433530208281⟩, ⟨(-617084946546928623), (-606801440002295635)⟩, true⟩

def words04 : List Nat := [371285362335407352, 371285362339281093, 371285362306878762, 371285362325089496, 371285362327834381, 371285362329066389, 371285362311190199, 371285362349942836, 371285362476640030, 371285362541023558]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk999A
