import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk952A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk952B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk952A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk952B
