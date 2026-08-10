import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk597A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk597A
