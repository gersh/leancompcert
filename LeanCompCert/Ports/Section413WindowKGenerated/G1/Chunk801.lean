import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk801

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479999373543253, 362480095591967990⟩, ⟨401520004590932711, 406724293740845785⟩, true⟩

def state01 : KState := ⟨⟨362475221887813827, 362475318130937371⟩, ⟨784229888557520835, 789436156207375859⟩, true⟩

def words00 : List Nat := [371285173238118984, 371285173240906738, 371285173106165243, 371285172972379599, 371285172837495716, 371285172730536945, 371285172567308302, 371285172560964263, 371285172553683980, 371285172533087008]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490594947827776, 362490691215986082⟩, ⟨(-447374358275011156), (-442166084960913286)⟩, true⟩

def words01 : List Nat := [371285172444666401, 371285172480728075, 371285172595192615, 371285172597962882, 371285172532048183, 371285172432634831, 371285172375408210, 371285172378488569, 371285172414984058, 371285172487001660]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477298125580646, 362477394418747099⟩, ⟨618029974804258090, 623240251900053476⟩, true⟩

def words02 : List Nat := [371285172538843862, 371285172541662234, 371285172529783146, 371285172583766930, 371285172682859672, 371285172685629177, 371285172577336106, 371285172458027058, 371285172337586383, 371285172282866656]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471602308530945, 362471698626624022⟩, ⟨1074506435569720868, 1079718710158914922⟩, true⟩

def words03 : List Nat := [371285172226537647, 371285172268393483, 371285172309324020, 371285172312094069, 371285172161445128, 371285172016537421, 371285171870078103, 371285171864018651, 371285171697947932, 371285171532915000]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490957111675260, 362491053454590668⟩, ⟨(-476678447977085219), (-471464183998690037)⟩, true⟩

def words04 : List Nat := [371285171366678688, 371285171357202654, 371285171287814618, 371285171277504845, 371285171266326851, 371285171236802753, 371285171066818619, 371285171053802160, 371285171178631194, 371285171254942521]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490506738497630, 362490603106676320⟩, ⟨(-440560310560536689), (-435344021605490813)⟩, true⟩

def words05 : List Nat := [371285171330413882, 371285171406845151, 371285171637659088, 371285171803292263, 371285171941720778, 371285172081175936, 371285172162316829, 371285172165100704, 371285172164808141, 371285172236033421]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487300055320977, 362487396448154624⟩, ⟨(-183487330135847629), (-178269064709136145)⟩, true⟩

def words06 : List Nat := [371285172420722461, 371285172423493280, 371285172416361627, 371285172411012212, 371285172443979490, 371285172447035443, 371285172547748324, 371285172677952383, 371285172807208002, 371285172837812866]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497644808664354, 362497741226566997⟩, ⟨(-1012891729259022278), (-1007671453925876104)⟩, true⟩

def words07 : List Nat := [371285172904815735, 371285172973221908, 371285173195637496, 371285173211669634, 371285173213816790, 371285173207062139, 371285173344788812, 371285173448796536, 371285173607434531, 371285173767269584]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480811268938767, 362480907711855277⟩, ⟨336881393963592328, 342103675033111608⟩, true⟩

def words08 : List Nat := [371285173909981099, 371285173912753574, 371285173983843589, 371285174095208677, 371285174201681156, 371285174204452904, 371285174103804478, 371285174004113808, 371285173903328296, 371285173875654169]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467830321311955, 362467926789230400⟩, ⟨1377969970274621299, 1383194256372961081⟩, true⟩

def words09 : List Nat := [371285173926527867, 371285174031820481, 371285174136131482, 371285174138903599, 371285174051354579, 371285174000040650, 371285173980944971, 371285173983717131, 371285173812313390, 371285173600407121]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk801
