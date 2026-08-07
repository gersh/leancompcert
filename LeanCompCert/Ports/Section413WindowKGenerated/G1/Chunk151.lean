import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk151

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362397379572965374, 362397382550521165⟩, ⟨1310391970090477019, 1310422384667474703⟩, true⟩

def state01 : KState := ⟨⟨362493568703149550, 362493571684800566⟩, ⟨(-142392441767663415), (-142361965331600019)⟩, true⟩

def words00 : List Nat := [371284159743380143, 371284158371946061, 371284154804999605, 371284153432748961, 371284152060532958, 371284150291516920, 371284146352531957, 371284146568700607, 371284149979142869, 371284150603116257]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362451439920529697, 362451442906368374⟩, ⟨494452770252793887, 494483309984639685⟩, true⟩

def words01 : List Nat := [371284150960564461, 371284151318119138, 371284152278332459, 371284152278839950, 371284152486121157, 371284153259412255, 371284154033948038, 371284154034406099, 371284148991499716, 371284146828986406]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362389408572438342, 362389411562352577⟩, ⟨1432822737843703057, 1432853339219192707⟩, true⟩

def words02 : List Nat := [371284146864637347, 371284146865095472, 371284143249041393, 371284139503118188, 371284135757521654, 371284132213100335, 371284126489416575, 371284122571371916, 371284118653690511, 371284114360714718]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362560666501203234, 362560669495259698⟩, ⟨(-1159156275012065840), (-1159125610943767540)⟩, true⟩

def words03 : List Nat := [371284108102167220, 371284106199278281, 371284105685081540, 371284105685548711, 371284104540707346, 371284102661337030, 371284103253846832, 371284103960984640, 371284109018465183, 371284114075476080]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472259306597431, 362472262304797410⟩, ⟨179538003432523440, 179568730255038388⟩, true⟩

def words04 : List Nat := [371284118216641722, 371284118217100638, 371284119854817223, 371284122246793885, 371284125345721796, 371284125346180741, 371284122648260606, 371284118658672976, 371284115025742983, 371284115026266390]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362454559575549907, 362454562577885188⟩, ⟨447945247597877857, 447976037091656229⟩, true⟩

def words05 : List Nat := [371284117316620423, 371284120389066492, 371284123462158257, 371284123462617330, 371284120745222488, 371284118200967431, 371284116236069370, 371284116236533891, 371284114397215009, 371284112448405746]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478305329990704, 362478308336443583⟩, ⟨88271834495194564, 88302686432521114⟩, true⟩

def words06 : List Nat := [371284112888472635, 371284114050055958, 371284118621918019, 371284123193359976, 371284126999294083, 371284126999753532, 371284126236698558, 371284127449757207, 371284129211803641, 371284129212279610]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495226556651798, 362495229567287399⟩, ⟨(-168359312196124030), (-168328396785736764)⟩, true⟩

def words07 : List Nat := [371284128828940926, 371284128376329519, 371284131801021698, 371284133598706559, 371284136644020789, 371284139689120745, 371284142735173660, 371284142735633452, 371284140739527051, 371284141470535819]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362441713695564065, 362441716710301392⟩, ⟨644075240874560174, 644106218570532622⟩, true⟩

def words08 : List Nat := [371284143727011473, 371284143727471557, 371284140214502660, 371284135799006234, 371284131383908012, 371284128294194227, 371284123041900340, 371284122112048326, 371284121182168504, 371284120016329736]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506528878678801, 362506531897581051⟩, ⟨(-340813195000315842), (-340782154018453288)⟩, true⟩

def words09 : List Nat := [371284117225300717, 371284116613279053, 371284119707292700, 371284119707753116, 371284118440127613, 371284116453783571, 371284114467525346, 371284113385085185, 371284112018502443, 371284113493922183]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk151
