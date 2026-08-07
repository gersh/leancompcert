import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk074

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479805160918510, 362479805830704069⟩, ⟨47313101630562768, 47316458128418564⟩, true⟩

def state01 : KState := ⟨⟨362406570781247969, 362406571452931929⟩, ⟨588976532878136363, 588979903433941185⟩, true⟩

def words00 : List Nat := [371286199082872006, 371286198297784154, 371286173304328609, 371286157787745173, 371286142275252021, 371286132178072312, 371286109657844859, 371286086910507655, 371286064169223638, 371286055920331922]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362387966860830748, 362387967534414302⟩, ⟨727549669548478281, 727553054190070545⟩, true⟩

def words01 : List Nat := [371286052558372215, 371286059919710993, 371286063362978627, 371286063363191006, 371286050702091907, 371286043449379115, 371286047012628166, 371286047012839260, 371286033722905970, 371286020506677115]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362323976104246870, 362323976779720832⟩, ⟨1203367544445249532, 1203370943123443862⟩, true⟩

def words02 : List Nat := [371286007399662056, 371286007399894510, 371286000917650421, 371286003422479937, 371286003422646490, 371286000453775605, 371285978056653260, 371285963164526936, 371285948276304675, 371285937875699762]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362355744619774338, 362355745297178035⟩, ⟨967544984803282958, 967548397829029626⟩, true⟩

def words03 : List Nat := [371285916080528332, 371285894368595165, 371285872662417059, 371285868940948536, 371285858730188579, 371285853910020198, 371285849091076849, 371285841329541370, 371285809606341102, 371285792124843228]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362224854969559681, 362224855648852114⟩, ⟨1942076640790470980, 1942080067878235768⟩, true⟩

def words04 : List Nat := [371285774647926485, 371285764680763214, 371285732821511983, 371285700819378837, 371285668825764265, 371285642245587092, 371285609020747398, 371285585203017831, 371285561391606915, 371285537537157918]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467079365597075, 362467080046803539⟩, ⟨136167683086871939, 136171124443936777⟩, true⟩

def words05 : List Nat := [371285502551140845, 371285485451416599, 371285468356172094, 371285464101245705, 371285435995708924, 371285403468851116, 371285370950628992, 371285356283620967, 371285335995681967, 371285333548739724]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362306936634361387, 362306937317488548⟩, ⟨1331928987084461639, 1331932442779866109⟩, true⟩

def words06 : List Nat := [371285331102378092, 371285328538163953, 371285316569464827, 371285315863466857, 371285319885393175, 371285319885605760, 371285300838233581, 371285280993191352, 371285261153382895, 371285241526696027]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362217939940746022, 362217940625792261⟩, ⟨1997715203409401283, 1997718673450020975⟩, true⟩

def words07 : List Nat := [371285217660663839, 371285208214093872, 371285198769978606, 371285188320886570, 371285157953613796, 371285128262254918, 371285098578727192, 371285086652564954, 371285051024459894, 371285015314756168]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362414459427295280, 362414460114252514⟩, ⟨526868251153617214, 526871735498182030⟩, true⟩

def words08 : List Nat := [371284979614501586, 371284961655857305, 371284937161414736, 371284920143140438, 371284903129349669, 371284883318024410, 371284845637735271, 371284825675519892, 371284805718519900, 371284803470126771]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362412612201310547, 362412612890207967⟩, ⟨540681701957727263, 540685200844369917⟩, true⟩

def words09 : List Nat := [371284794079905176, 371284780397252283, 371284766718167540, 371284766494720630, 371284757397157012, 371284753713692485, 371284750031142116, 371284741142643610, 371284713863522135, 371284704250320550]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk074
