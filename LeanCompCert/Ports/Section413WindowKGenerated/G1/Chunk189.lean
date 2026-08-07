import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk189

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362452509207747826, 362452513966682274⟩, ⟨640032171613454451, 640093006904533799⟩, true⟩

def state01 : KState := ⟨⟨362411076990404525, 362411081754535270⟩, ⟨1423484058824436175, 1423544992352470709⟩, true⟩

def words00 : List Nat := [371286379853235577, 371286379853822141, 371286377534143364, 371286375222001379, 371286372909875552, 371286371303944921, 371286368544364793, 371286366448474303, 371286364352620765, 371286361764707268]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362544667428899285, 362544672198316203⟩, ⟨(-1103343048053506504), (-1103282014537200478)⟩, true⟩

def words01 : List Nat := [371286357784351717, 371286356590828484, 371286356988953892, 371286356989548395, 371286356334166748, 371286355232583231, 371286355813662322, 371286356112125766, 371286359194768354, 371286362277353400]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473091092481787, 362473095867177482⟩, ⟨251046205632689322, 251107339050503816⟩, true⟩

def words02 : List Nat := [371286364603227735, 371286364603812314, 371286364135943139, 371286365057789948, 371286366805936583, 371286366806521313, 371286364841577849, 371286362879804606, 371286360917981029, 371286360914142644]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362412677728231931, 362412682508180937⟩, ⟨1395114678065697500, 1395175910956243188⟩, true⟩

def words03 : List Nat := [371286360951973463, 371286361690660306, 371286362440320785, 371286362440905782, 371286359481184039, 371286356611641410, 371286353742089413, 371286352955133231, 371286349327898325, 371286345439065639]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362425311990315094, 362425316775511549⟩, ⟨1155936092832273251, 1155997425136121587⟩, true⟩

def words04 : List Nat := [371286341550392568, 371286338982827271, 371286335700657112, 371286334435781712, 371286333170853875, 371286331459040957, 371286326042550742, 371286323401738471, 371286320760916428, 371286319278157255]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362413588145597974, 362413592936136400⟩, ⟨1378203126583245606, 1378264560144147024⟩, true⟩

def words05 : List Nat := [371286316059635804, 371286312853185577, 371286309646833295, 371286307878797692, 371286305054231170, 371286302306837872, 371286299559532128, 371286296653759705, 371286290048128910, 371286286214625016]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362402458999236712, 362402463794999081⟩, ⟨1589318941939959318, 1589380474574141624⟩, true⟩

def words06 : List Nat := [371286282381191661, 371286280900501781, 371286276582365953, 371286271650064874, 371286266718061656, 371286262638323949, 371286257535852270, 371286254249221566, 371286250962735285, 371286247689283433]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466956403907383, 362466961204963326⟩, ⟨365525001145849588, 365586634225670688⟩, true⟩

def words07 : List Nat := [371286243273262389, 371286241160025166, 371286239699105868, 371286239699692494, 371286237162511605, 371286233614004870, 371286230065633557, 371286227675865737, 371286223896452967, 371286222882214416]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362420866398994280, 362420871205345708⟩, ⟨1240366235475407572, 1240427969090413634⟩, true⟩

def words08 : List Nat := [371286221867871502, 371286220536121535, 371286215514154482, 371286212598228296, 371286209682303763, 371286207618701542, 371286203076014027, 371286198547115750, 371286194018462952, 371286191266909185]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362371222164829750, 362371226976475813⟩, ⟨2183427832388916633, 2183489666576237877⟩, true⟩

def words09 : List Nat := [371286187827787490, 371286185548117605, 371286183268485024, 371286180966326753, 371286174979444661, 371286169415456860, 371286163851761362, 371286159564100059, 371286153533343064, 371286147485242984]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk189
