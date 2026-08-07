import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk691

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362463043383019965, 362463114173358780⟩, ⟨1537984446044559396, 1541288110358465852⟩, true⟩

def state01 : KState := ⟨⟨362475661469747655, 362475732281248076⟩, ⟨666048802930520935, 669353929618741695⟩, true⟩

def words00 : List Nat := [371285419034665301, 371285418889169439, 371285418669619130, 371285418605640429, 371285418540856350, 371285418423959485, 371285418053074830, 371285417840395345, 371285417626509350, 371285417622437756]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474345138817227, 362474415971912789⟩, ⟨756995436071439088, 760302055304240904⟩, true⟩

def words01 : List Nat := [371285417484110145, 371285417308788779, 371285417132500156, 371285417023853555, 371285416809492035, 371285416618136458, 371285416426008160, 371285416234919180, 371285415868443782, 371285415712296242]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474228344204197, 362474299198333239⟩, ⟨765088436813025594, 768396509990267104⟩, true⟩

def words02 : List Nat := [371285415554769543, 371285415531222030, 371285415352557669, 371285415175101796, 371285414996780856, 371285414832720054, 371285414576970748, 371285414531084519, 371285414484396660, 371285414437881775]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490933658090003, 362491004533603621⟩, ⟨(-389788341237176821), (-386478789636236639)⟩, true⟩

def words03 : List Nat := [371285414304787108, 371285414333725419, 371285414550534613, 371285414568377930, 371285414570219631, 371285414524151273, 371285414603631509, 371285414648229109, 371285414730714625, 371285414814194931]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494695519695502, 362494766416527749⟩, ⟨(-649962558284633826), (-646651532604819388)⟩, true⟩

def words04 : List Nat := [371285414889158541, 371285414891523320, 371285414735367782, 371285414763726851, 371285414854855901, 371285414857278337, 371285414833237309, 371285414814304887, 371285414981685414, 371285415119618018]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482129751248273, 362482200669440332⟩, ⟨219092957064242494, 222405459878143404⟩, true⟩

def words05 : List Nat := [371285415465174725, 371285415811717477, 371285416102954824, 371285416144130765, 371285416248555012, 371285416354154254, 371285416566572490, 371285416568937787, 371285416523777307, 371285416480022723]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481964105893401, 362482035045232227⟩, ⟨230587977450607889, 233901942883665589⟩, true⟩

def words06 : List Nat := [371285416489225194, 371285416491831568, 371285416600950820, 371285416761578053, 371285416885915556, 371285416888280980, 371285416734012589, 371285416622703679, 371285416594654135, 371285416597102745]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472513399872289, 362472584360729043⟩, ⟨884385650738425382, 887701104677358182⟩, true⟩

def words07 : List Nat := [371285416549983963, 371285416504055508, 371285416493479173, 371285416496159400, 371285416488706314, 371285416518945712, 371285416548789407, 371285416551155085, 371285416302558330, 371285416119975608]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464796890455579, 362464867872421737⟩, ⟨1418216773375485396, 1421533687769727738⟩, true⟩

def words08 : List Nat := [371285415936127188, 371285415841081610, 371285415467199728, 371285415093785594, 371285414719437372, 371285414381752783, 371285413963774050, 371285413721252175, 371285413477914344, 371285413235736808]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493276014371559, 362493347017732793⟩, ⟨(-552377528343677381), (-549059133516790183)⟩, true⟩

def words09 : List Nat := [371285412940404749, 371285412854838279, 371285412888028995, 371285412890397566, 371285412785563264, 371285412635080559, 371285412539096595, 371285412541710063, 371285412634496688, 371285412751847665]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk691
