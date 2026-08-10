import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk705A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566219499370570, 360566251551336543⟩, ⟨1141588566032055456, 1143114880866780984⟩, true⟩

def state01 : KState := ⟨⟨360573060436952489, 360573092498320156⟩, ⟨659217049783159937, 660744027485972571⟩, true⟩

def words00 : List Nat := [360582465717629441, 360582465689386222, 360582465460164220, 360582465109821383, 360582464759308478, 360582464316172251, 360582463973224070, 360582463831196694, 360582463689066521, 360582463424819745]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591189913595337, 360591221984404363⟩, ⟨(-619277499317053637), (-617749855858567859)⟩, true⟩

def words01 : List Nat := [360582463292741790, 360582463151591425, 360582463029145452, 360582463030144651, 360582462849250365, 360582462497026862, 360582462144619255, 360582461955913563, 360582462059151107, 360582462184403533]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579770204699649, 360579802285022799⟩, ⟨185961370708070045, 187489685149542217⟩, true⟩

def words02 : List Nat := [360582462185300020, 360582462157540301, 360582462039279129, 360582462063026422, 360582462063883147, 360582461914846853, 360582461606763441, 360582461198319403, 360582460789692624, 360582460581990750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360562857480995917, 360562889570742778⟩, ⟨1378940749647945278, 1380469728791917988⟩, true⟩

def words03 : List Nat := [360582460673083527, 360582460802078041, 360582460802979401, 360582460792160160, 360582460580480393, 360582460318565616, 360582460056365020, 360582459994899252, 360582459874486957, 360582459598086015]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588250240223481, 360588282339403018⟩, ⟨(-412446987950902225), (-410917343379164095)⟩, true⟩

def words04 : List Nat := [360582459321467659, 360582459139611215, 360582459057735699, 360582458971666129, 360582458885521456, 360582458628388165, 360582458376502952, 360582458136102875, 360582457895416328, 360582457938000074]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk705A
