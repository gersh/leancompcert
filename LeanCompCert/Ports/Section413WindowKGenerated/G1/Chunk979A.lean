import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk979A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482795573276342, 362482941547878048⟩, ⟨225852392135917734, 235500890812924164⟩, true⟩

def state01 : KState := ⟨⟨362481064505586844, 362481210510990860⟩, ⟨395378443760985923, 405029958136893661⟩, true⟩

def words00 : List Nat := [371285347113574480, 371285347143359504, 371285347216241703, 371285347290553541, 371285347343037307, 371285347346475141, 371285347259579682, 371285347251171745, 371285347265251347, 371285347268810663]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483043474032599, 362483189510836581⟩, ⟨201604645468706502, 211259234363501950⟩, true⟩

def words01 : List Nat := [371285347229176604, 371285347163621452, 371285347121659206, 371285347125448444, 371285347105289297, 371285347113556710, 371285347116786801, 371285347120225261, 371285346996174932, 371285346978507777]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486499507085481, 362486645574539703⟩, ⟨(-136819350532793073), (-127161760203827773)⟩, true⟩

def words02 : List Nat := [371285347032868207, 371285347036330116, 371285347019547394, 371285346983623489, 371285346946416320, 371285346942605960, 371285346953482325, 371285347013681903, 371285347074438296, 371285347091319846]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491735720319582, 362491881818786474⟩, ⟨(-649614484879160051), (-639953857317390361)⟩, true⟩

def words03 : List Nat := [371285347211233309, 371285347332891529, 371285347485008283, 371285347525330151, 371285347548685688, 371285347573157564, 371285347613888033, 371285347617713915, 371285347673057402, 371285347743605321]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486203914925665, 362486350044417678⟩, ⟨(-107818495752715312), (-98154829436871364)⟩, true⟩

def words04 : List Nat := [371285347812707059, 371285347816162873, 371285347856616117, 371285347932076848, 371285348030193926, 371285348033633339, 371285347992977922, 371285347953525780, 371285347949325572, 371285347963484999]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk979A
