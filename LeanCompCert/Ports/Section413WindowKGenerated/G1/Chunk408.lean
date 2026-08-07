import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk408

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468415031900975, 362468438691277284⟩, ⟨681416919763949069, 682069194852610537⟩, true⟩

def state01 : KState := ⟨⟨362457644113574205, 362457667784895914⟩, ⟨1120953505664086365, 1121606268186990027⟩, true⟩

def words00 : List Nat := [371285155854903304, 371285155856244889, 371285155400890404, 371285154749259355, 371285154097159942, 371285153626134666, 371285152855310546, 371285152392066040, 371285151928381002, 371285151398426593]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481253432737220, 362481277116143176⟩, ⟨157361882175341944, 158015137918529258⟩, true⟩

def words01 : List Nat := [371285150725900229, 371285150525204311, 371285150721182570, 371285150722522919, 371285150321534445, 371285149820338944, 371285149318624726, 371285148925384940, 371285148231964280, 371285148138630157]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362459035999912730, 362459059695407262⟩, ⟨1064282829582865886, 1064936578842485138⟩, true⟩

def words02 : List Nat := [371285148044809959, 371285147835538801, 371285146826764943, 371285146418165506, 371285146008870720, 371285145646275423, 371285144552226075, 371285143469840012, 371285142386974096, 371285141904049008]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362446519847542998, 362446543555139196⟩, ⟨1575398807072621244, 1576053050504385662⟩, true⟩

def words03 : List Nat := [371285141266192243, 371285140781221415, 371285140295806169, 371285139792987671, 371285138676192665, 371285137740407978, 371285136803989167, 371285136358950928, 371285135415579087, 371285134472144691]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476617098132318, 362476640817733338⟩, ⟨346084644610091419, 346739378379589145⟩, true⟩

def words04 : List Nat := [371285133528148575, 371285133183698200, 371285132540198620, 371285132116069360, 371285131691573773, 371285131116386441, 371285129970588227, 371285129424361092, 371285128928417548, 371285128929811174]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362475054699891955, 362475078431723373⟩, ⟨410000381820769203, 410655615264542211⟩, true⟩

def words05 : List Nat := [371285128723045055, 371285128432571273, 371285128448323202, 371285128546291190, 371285128823911873, 371285129102043930, 371285129379221391, 371285129380564236, 371285128984781266, 371285128740466999]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462354944611847, 362462378688391454⟩, ⟨928975726942603630, 929631448651408404⟩, true⟩

def words06 : List Nat := [371285128685793784, 371285128687135728, 371285128080920050, 371285127457161746, 371285126832908527, 371285126236893496, 371285125422988972, 371285125207942092, 371285124992472997, 371285124747815272]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488137132197580, 362488160888145342⟩, ⟨(-124908954376344340), (-124252735295010456)⟩, true⟩

def words07 : List Nat := [371285124192194465, 371285124065562437, 371285124057367757, 371285124058710181, 371285123461021757, 371285122786032294, 371285122110533349, 371285121884411519, 371285121436121544, 371285121512022082]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362454431603258558, 362454455371302110⟩, ⟨1253077837207596039, 1253734550827514947⟩, true⟩

def words08 : List Nat := [371285121586961136, 371285121588303619, 371285120866339131, 371285120742840936, 371285120618708452, 371285120476492849, 371285119537322448, 371285118367097565, 371285117196370257, 371285116524416014]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475800665089802, 362475824445219833⟩, ⟨379253944548021445, 379911152445035803⟩, true⟩

def words09 : List Nat := [371285115775501017, 371285115542309468, 371285115308689008, 371285115058506567, 371285114428625641, 371285113979564586, 371285113676403124, 371285113677761906, 371285113452070829, 371285113226453208]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk408
