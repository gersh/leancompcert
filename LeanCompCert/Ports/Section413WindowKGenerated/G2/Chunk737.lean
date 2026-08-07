import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk737

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

def state06 : KState := ⟨⟨360589694533988722, 360589729744856449⟩, ⟨(-542058762820354132), (-540304554744847578)⟩, true⟩

def words05 : List Nat := [360582404132357260, 360582404228995725, 360582404468655361, 360582404524891174, 360582404525873969, 360582404393672647, 360582404311551885, 360582404473385038, 360582404573560264, 360582404673955230]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598187673250714, 360598222894105271⟩, ⟨(-1168679635295092760), (-1166924690540749118)⟩, true⟩

def words06 : List Nat := [360582404674890991, 360582404659275367, 360582404589015199, 360582404581772645, 360582404574240624, 360582404560191575, 360582404561126231, 360582404488528989, 360582404474981118, 360582404690603343]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561672987885645, 360561708218633919⟩, ⟨1525267252003492423, 1527022926665497739⟩, true⟩

def words07 : List Nat := [360582405089324858, 360582405488236380, 360582405745666321, 360582405819637906, 360582405820520984, 360582405783991918, 360582405747162417, 360582405662540731, 360582405474558846, 360582405195140635]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584783767716078, 360584819008361895⟩, ⟨(-179932480636561135), (-178176075686012953)⟩, true⟩

def words08 : List Nat := [360582404915469755, 360582404775168513, 360582404859191473, 360582404993523565, 360582404994491126, 360582404971714893, 360582404812599176, 360582404615162735, 360582404417410192, 360582404403929295]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575346730353639, 360575381980997829⟩, ⟨516529629597504288, 518286772376642460⟩, true⟩

def words09 : List Nat := [360582404404873792, 360582404344325197, 360582404373450103, 360582404610649714, 360582404801245836, 360582404992010065, 360582405052704873, 360582405053754052, 360582404930944236, 360582404836992093]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk737
