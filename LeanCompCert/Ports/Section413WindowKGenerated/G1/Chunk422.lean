import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk422

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362519920336727509, 362519945716807116⟩, ⟨(-1468498187006250164), (-1467774495187544190)⟩, true⟩

def state01 : KState := ⟨⟨362488181994112345, 362488207386748524⟩, ⟨(-129094141278716955), (-128369919508543807)⟩, true⟩

def words00 : List Nat := [371285165975462651, 371285166048292476, 371285166352016107, 371285166656412649, 371285167022684943, 371285167024075147, 371285166751387081, 371285166369268174, 371285166164569346, 371285166238244378]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362462780116402383, 362462805521524414⟩, ⟨943289615879161223, 944014364742774999⟩, true⟩

def words01 : List Nat := [371285166540573394, 371285166843433413, 371285167144538003, 371285167145927979, 371285166699265381, 371285166421531430, 371285166143096541, 371285165989654407, 371285165461347421, 371285164933289994]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490617806357804, 362490643223934569⟩, ⟨(-232048011908512184), (-231322737146273882)⟩, true⟩

def words02 : List Nat := [371285164436371482, 371285164437904130, 371285164580822580, 371285164933976901, 371285165181850331, 371285165183241324, 371285164944394851, 371285165106758880, 371285165535136179, 371285165666283880]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362505823602180687, 362505849032455296⟩, ⟨(-874289874538375419), (-873564063484088061)⟩, true⟩

def words03 : List Nat := [371285165685904057, 371285165705986593, 371285166218543473, 371285166451927347, 371285166853016967, 371285167254606873, 371285167642545118, 371285167643960392, 371285168063289171, 371285168554637913]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489634908850417, 362489660351494176⟩, ⟨(-190390858639311166), (-189664525047094386)⟩, true⟩

def words04 : List Nat := [371285169517966684, 371285169734964161, 371285169950277639, 371285170166037801, 371285170301341341, 371285170302887803, 371285170522015467, 371285170886272563, 371285171248861215, 371285171356558031]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499456381337513, 362499481836553757⟩, ⟨(-605424853888485889), (-604697989044299205)⟩, true⟩

def words05 : List Nat := [371285171616424033, 371285171877002818, 371285172435464038, 371285172436856100, 371285172350410261, 371285172178981053, 371285172394363250, 371285172503746153, 371285172843309092, 371285173183444643]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362500474571208801, 362500500038974564⟩, ⟨(-648501536479536392), (-647774141227293922)⟩, true⟩

def words06 : List Nat := [371285173521861360, 371285173523266147, 371285173864737056, 371285174218879443, 371285174715173409, 371285174747799464, 371285174799647571, 371285174851949950, 371285175359336477, 371285175723457371]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473455287794843, 362473480768128212⟩, ⟨493833034809693282, 494560961357938316⟩, true⟩

def words07 : List Nat := [371285176510534047, 371285177298157914, 371285177872058722, 371285177873452801, 371285177915557505, 371285177985938571, 371285178526088021, 371285178527480275, 371285178322317733, 371285178047252099]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486247859061511, 362486273351850471⟩, ⟨(-46962470097038447), (-46234016862202157)⟩, true⟩

def words08 : List Nat := [371285178054538847, 371285178112839868, 371285178730145957, 371285179347987101, 371285179882001647, 371285179883394046, 371285179688833301, 371285179707243870, 371285180089192360, 371285180116484502]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492378474179779, 362492403979648098⟩, ⟨(-306223223258013735), (-305494233750303723)⟩, true⟩

def words09 : List Nat := [371285180117535864, 371285180081682935, 371285180567295285, 371285180945598443, 371285181347638315, 371285181750201603, 371285182107483920, 371285182108876873, 371285181892017183, 371285182064474691]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk422
