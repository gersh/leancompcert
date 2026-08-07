import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk597

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502629652904048, 362502681889295994⟩, ⟨(-1050994107590656260), (-1048887598672859214)⟩, true⟩

def state01 : KState := ⟨⟨362499125527354687, 362499177781762082⟩, ⟨(-841786161870301000), (-839678577336972098)⟩, true⟩

def words00 : List Nat := [371285113415462119, 371285113580310355, 371285113693730607, 371285113807826157, 371285114005284070, 371285114086115532, 371285114447117114, 371285114808927889, 371285115167386675, 371285115405025184]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362506083643180146, 362506135915842091⟩, ⟨(-1257245201682458059), (-1255136527077018367)⟩, true⟩

def words01 : List Nat := [371285115826716604, 371285116249468843, 371285116930405745, 371285117282599606, 371285117588372219, 371285117894730309, 371285118279915916, 371285118538690387, 371285118892002686, 371285119246210354]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362502058488997864, 362502110779900914⟩, ⟨(-1016899048045363011), (-1014789283989392583)⟩, true⟩

def words02 : List Nat := [371285119567462076, 371285119621795649, 371285119956400521, 371285120292085716, 371285120712885709, 371285120760375949, 371285120802971514, 371285120846273212, 371285121169611592, 371285121456367249]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484492333899411, 362484544642988604⟩, ⟨32420274163869140, 34531124570561458⟩, true⟩

def words03 : List Nat := [371285121799758983, 371285122143916152, 371285122488272604, 371285122490293704, 371285122482039235, 371285122505785677, 371285122678642965, 371285122680704984, 371285122673922537, 371285122666499997]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362495244739714166, 362495297066885087⟩, ⟨(-609958094774256552), (-607846164071532252)⟩, true⟩

def words04 : List Nat := [371285122790819582, 371285122793067841, 371285123060841994, 371285123336634130, 371285123532568173, 371285123534589783, 371285123458037132, 371285123561841104, 371285123907232223, 371285124079586607]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488534461888463, 362488586807542914⟩, ⟨(-208920749671201285), (-206807714487705189)⟩, true⟩

def words05 : List Nat := [371285124249192319, 371285124419530608, 371285124869629919, 371285125202774429, 371285125522738413, 371285125843439690, 371285126162167491, 371285126164189541, 371285126167194410, 371285126227658245]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475318211782973, 362475370575431489⟩, ⟨580951560966851663, 583065671570291473⟩, true⟩

def words06 : List Nat := [371285126471291089, 371285126473313221, 371285126343636582, 371285126163235206, 371285125982083861, 371285125885808333, 371285125709921103, 371285125736490090, 371285125738017604, 371285125731388831]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362508846514948199, 362508898896902781⟩, ⟨(-1423198329332314484), (-1421083124485419138)⟩, true⟩

def words07 : List Nat := [371285125686782012, 371285125806412377, 371285126039302667, 371285126140366668, 371285126193779568, 371285126247847256, 371285126493704965, 371285126613265150, 371285127012300098, 371285127412242347]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489011911465075, 362489064311640521⟩, ⟨(-237413101276758356), (-235296807092207084)⟩, true⟩

def words08 : List Nat := [371285127810162499, 371285127874328108, 371285128196059969, 371285128518848221, 371285128855335223, 371285128857358215, 371285128855504823, 371285128820469358, 371285128922026189, 371285128990152468]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362495629827619247, 362495682246042070⟩, ⟨(-633060770561636152), (-630943385277068344)⟩, true⟩

def words09 : List Nat := [371285129337588447, 371285129685863270, 371285130027063260, 371285130137395503, 371285130331106952, 371285130525828573, 371285130999682969, 371285131173050756, 371285131351003940, 371285131529745068]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk597
