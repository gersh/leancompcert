import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk737A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360606166801035892, 360606201952380891⟩, ⟨(-1755532136699712771), (-1753782317229716579)⟩, true⟩

def state01 : KState := ⟨⟨360593847256578275, 360593882417921370⟩, ⟨(-847670704795320129), (-845920148420074647)⟩, true⟩

def words00 : List Nat := [360582406253668881, 360582406350471353, 360582406443073408, 360582406535966313, 360582406582097320, 360582406583145180, 360582406492004081, 360582406296666106, 360582406101132867, 360582406245458372]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561971470046491, 360562006641250511⟩, ⟨1502059507567202494, 1503810790841397930⟩, true⟩

def words01 : List Nat := [360582406430501989, 360582406615738314, 360582406709105084, 360582406710153009, 360582406619679604, 360582406432005061, 360582406244042992, 360582406052298743, 360582405869545679, 360582405593920634]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587832792639340, 360587867973735668⟩, ⟨(-404548662134928434), (-402796649549323838)⟩, true⟩

def words02 : List Nat := [360582405318063264, 360582405270795065, 360582405314991542, 360582405359401436, 360582405360369303, 360582405247492362, 360582404992720881, 360582404921963474, 360582404850892054, 360582404916818641]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586986944897699, 360587022135988248⟩, ⟨(-342237184794614214), (-340484435284624702)⟩, true⟩

def words03 : List Nat := [360582404917768877, 360582404850028649, 360582404782095352, 360582404795418627, 360582404802286168, 360582404809329385, 360582404810273026, 360582404725674687, 360582404770603734, 360582404834415384]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575872428305287, 360575907629267927⟩, ⟨477363018605999953, 479116496132280331⟩, true⟩

def words04 : List Nat := [360582405003045664, 360582405004093988, 360582404989138253, 360582404867649383, 360582404746001753, 360582404482995989, 360582404351343908, 360582404319226576, 360582404287001213, 360582404124130738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk737A
