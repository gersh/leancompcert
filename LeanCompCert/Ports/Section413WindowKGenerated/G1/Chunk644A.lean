import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk644A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498273862165988, 362498335011701591⟩, ⟨(-827935205908632769), (-825275351825568761)⟩, true⟩

def state01 : KState := ⟨⟨362485084367372803, 362485145536649476⟩, ⟨21511779390918301, 24172904901188371⟩, true⟩

def words00 : List Nat := [371285520575932162, 371285520578133142, 371285520757133108, 371285520969098788, 371285521190705858, 371285521192896468, 371285521093352156, 371285520948000385, 371285520831535529, 371285520834039652]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482070174664561, 362482131363652398⟩, ⟨215727650276768570, 218390045482613692⟩, true⟩

def words01 : List Nat := [371285521006976121, 371285521186604179, 371285521333537925, 371285521335768185, 371285521334319148, 371285521357817969, 371285521568421004, 371285521570613948, 371285521510786851, 371285521460601834]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480614464197688, 362480675672832299⟩, ⟨309532079054975088, 312195740006100626⟩, true⟩

def words02 : List Nat := [371285521456499820, 371285521458939303, 371285521488623852, 371285521592229508, 371285521655930888, 371285521658122338, 371285521400570850, 371285521267628931, 371285521173273711, 371285521175548520]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493352325391524, 362493413554011005⟩, ⟨(-511239085529387727), (-508574136851794753)⟩, true⟩

def words03 : List Nat := [371285521101997966, 371285521029637452, 371285521122527940, 371285521171128151, 371285521226591695, 371285521282845775, 371285521331574748, 371285521333783725, 371285521339319337, 371285521464551627]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483774616052469, 362483835864230937⟩, ⟨106051273194862301, 108717482354133537⟩, true⟩

def words04 : List Nat := [371285521746713432, 371285521829714624, 371285521911361928, 371285521993726828, 371285522148305054, 371285522204242169, 371285522393948676, 371285522584574070, 371285522711956656, 371285522714228674]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk644A
