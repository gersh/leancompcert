import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk952

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579764338916875, 360579824172797439⟩, ⟨219045915218144208, 222892277482533526⟩, true⟩

def state01 : KState := ⟨⟨360582645027839158, 360582704874732917⟩, ⟨(-55176956211798137), (-51329355027686049)⟩, true⟩

def words00 : List Nat := [360582165454756542, 360582165512395289, 360582165690422185, 360582165868710069, 360582165935849785, 360582165937229745, 360582165915876784, 360582165847067368, 360582165777856364, 360582165763127875]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583298193471059, 360583358053518323⟩, ⟨(-117362473000981868), (-113513619407754008)⟩, true⟩

def words01 : List Nat := [360582165764368722, 360582165702357903, 360582165686984238, 360582165821079363, 360582165911314931, 360582166001783343, 360582166015181267, 360582166016561356, 360582165932420368, 360582165946531338]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569497733903496, 360569557606960403⟩, ⟨1196733161577137858, 1200583254013118866⟩, true⟩

def words02 : List Nat := [360582165947666435, 360582165933878532, 360582165845974633, 360582165702820904, 360582165559451697, 360582165355673395, 360582165220231583, 360582165099747215, 360582164979100051, 360582164802739182]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360605430491712569, 360605490377797272⟩, ⟨(-2225352700210696874), (-2221501367074486572)⟩, true⟩

def words03 : List Nat := [360582164671469178, 360582164650877335, 360582164718032319, 360582164769774700, 360582164771069596, 360582164717365276, 360582164696271986, 360582164832491035, 360582165078519894, 360582165324857105]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581731712209858, 360581791611448394⟩, ⟨31812294320228718, 35664880291800156⟩, true⟩

def words04 : List Nat := [360582165506589197, 360582165691054997, 360582165874913696, 360582166059172085, 360582166197097301, 360582166225369209, 360582166226613059, 360582166185192616, 360582166143535491, 360582166045887154]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360558904272113689, 360558964184352873⟩, ⟨2206244665487057982, 2210098489835546938⟩, true⟩

def words05 : List Nat := [360582166043080295, 360582166019851208, 360582165996471727, 360582165917876808, 360582165759380260, 360582165573237414, 360582165386649718, 360582165310548555, 360582165124450347, 360582164882335611]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588528386898446, 360588588312183937⟩, ⟨(-615931914422714779), (-612076847219598803)⟩, true⟩

def words06 : List Nat := [360582164639902746, 360582164508093235, 360582164430759308, 360582164327000547, 360582164223143052, 360582164024084654, 360582163830869368, 360582163748270980, 360582163665264792, 360582163724983010]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583377186226223, 360583437124652232⟩, ⟨(-125149460692319830), (-121293141526270396)⟩, true⟩

def words07 : List Nat := [360582163726221332, 360582163712503681, 360582163793614125, 360582163959543160, 360582164065625774, 360582164171929658, 360582164186179124, 360582164187560163, 360582164105218497, 360582164120154733]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594729824538956, 360594789775971363⟩, ⟨(-1206885760556017548), (-1203028202075980628)⟩, true⟩

def words08 : List Nat := [360582164223487160, 360582164349603879, 360582164419794736, 360582164490147217, 360582164491308712, 360582164500925072, 360582164643654867, 360582164786647179, 360582164858991749, 360582164992916553]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360612140806908738, 360612200771390121⟩, ⟨(-2866140118287645392), (-2862281316305032782)⟩, true⟩

def words09 : List Nat := [360582165123791403, 360582165255064195, 360582165402415728, 360582165547283014, 360582165598884642, 360582165650592860, 360582165793504624, 360582166022241089, 360582166338517531, 360582166655102726]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk952
