import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk175A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593017622227343, 360593019378449528⟩, ⟨(-157439643058323848), (-157418838587755550)⟩, true⟩

def state01 : KState := ⟨⟨360594153089344386, 360594154847659308⟩, ⟨(-177571160840669105), (-177550319736621453)⟩, true⟩

def words00 : List Nat := [360584024530416803, 360584024961066677, 360584027447784987, 360584029934261293, 360584029934467673, 360584029660814734, 360584026153223937, 360584021320557014, 360584016488377535, 360584015488414455]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622733894325460, 360622735654755397⟩, ⟨(-678285526972183114), (-678264648823776998)⟩, true⟩

def words01 : List Nat := [360584015488613194, 360584013990947870, 360584013296028919, 360584016606079726, 360584018531927935, 360584020457592510, 360584020748050900, 360584020748273595, 360584021918838987, 360584024128653932]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360543964882920309, 360543966645445773⟩, ⟨701836008273724230, 701856923146299788⟩, true⟩

def words02 : List Nat := [360584026235284251, 360584026235506528, 360584025113268960, 360584021264165256, 360584017415463854, 360584012704387055, 360584010176681364, 360584008701311420, 360584007226081768, 360584004119669750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360641133396169819, 360641135160793651⟩, ⟨(-1002113248584472434), (-1002092296917043952)⟩, true⟩

def words03 : List Nat := [360584001836039694, 360584001617871154, 360584003478464189, 360584005137644730, 360584005137853152, 360584003697894981, 360584002258059861, 360584000073039820, 360584003330636565, 360584006587912000]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576310167014941, 360576311933763430⟩, ⟨135109002060571971, 135129991004465877⟩, true⟩

def words04 : List Nat := [360584008185169511, 360584010067866420, 360584013995064971, 360584017921881303, 360584019347248307, 360584019347471071, 360584018937523485, 360584016900989784, 360584014864648995, 360584011648350580]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk175A
