import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk079

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362326095384663298, 362326096152806995⟩, ⟨1250291314393388271, 1250295423640778013⟩, true⟩

def state01 : KState := ⟨⟨362417990845703526, 362417991615878134⟩, ⟨524159261627008846, 524163386928967888⟩, true⟩

def words00 : List Nat := [371284341365420439, 371284337299876670, 371284325329780207, 371284320097166506, 371284314865802967, 371284306392360937, 371284280206928771, 371284269965004971, 371284259725558724, 371284257530786980]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362451199014808050, 362451199787053328⟩, ⟨261414427925092058, 261418569616238636⟩, true⟩

def words01 : List Nat := [371284249154531488, 371284241043292728, 371284236680944510, 371284236681194116, 371284233252092739, 371284233966972863, 371284233967146752, 371284231404956693, 371284211350046148, 371284207182206894]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483329632215924, 362483330406484145⟩, ⟨6919515597429688, 6923673320995788⟩, true⟩

def words02 : List Nat := [371284213119725472, 371284213119953224, 371284207234074638, 371284201078677986, 371284194924746904, 371284193424953789, 371284190560148916, 371284197058068433, 371284203505027258, 371284203505263590]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362578226831013573, 362578227607339128⟩, ⟨(-746405407122787910), (-746401233074132852)⟩, true⟩

def words03 : List Nat := [371284204264162858, 371284205133040187, 371284221843977726, 371284221844205363, 371284217442630339, 371284209255520509, 371284208714908806, 371284210572912056, 371284222414003800, 371284234252210790]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362523733356098829, 362523734134476979⟩, ⟨(-313805481339480127), (-313801290982516179)⟩, true⟩

def words04 : List Nat := [371284245961640633, 371284246556373947, 371284256006467561, 371284265454299923, 371284274825472135, 371284274825700159, 371284267756008529, 371284260666006586, 371284262273716417, 371284267238365482]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362456042700598807, 362456043481036018⟩, ⟨225261469136706782, 225265675873437570⟩, true⟩

def words05 : List Nat := [371284287980398447, 371284308717313986, 371284326394392284, 371284326646799878, 371284328978880101, 371284331310487172, 371284347128232983, 371284347128461426, 371284346744489064, 371284343189060320]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362577971527236100, 362577972309717560⟩, ⟨(-745508253776868707), (-745504030757357217)⟩, true⟩

def words06 : List Nat := [371284347171681829, 371284347171932951, 371284362452465290, 371284377960563474, 371284389890833673, 371284389891065900, 371284400365637317, 371284411884563311, 371284433535233103, 371284445270355202]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362452250131051465, 362452250915615020⟩, ⟨257180611649786325, 257184851274203971⟩, true⟩

def words07 : List Nat := [371284456840422214, 371284468407661210, 371284481404113325, 371284486594613125, 371284491148471950, 371284495701276119, 371284500106362958, 371284500106591632, 371284483632622297, 371284479593719557]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362405493519703022, 362405494306305219⟩, ⟨630732036710556945, 630736292614080093⟩, true⟩

def words08 : List Nat := [371284482040207674, 371284482040437675, 371284473912598464, 371284465802569586, 371284457694482456, 371284454317239270, 371284445394296782, 371284441979902389, 371284438566288290, 371284435018772564]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362607936206906368, 362607936995584247⟩, ⟨(-987579650660323564), (-987575378161835628)⟩, true⟩

def words09 : List Nat := [371284427724654231, 371284430308713804, 371284448495575637, 371284453811547413, 371284456692349308, 371284459572498626, 371284470286096087, 371284474640102275, 371284490073053314, 371284505502250685]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk079
