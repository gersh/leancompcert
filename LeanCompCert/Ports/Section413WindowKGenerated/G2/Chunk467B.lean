import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk467A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk467B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk467A

def state06 : KState := ⟨⟨360585716227572533, 360585729869145718⟩, ⟨(-132220803708608950), (-131789757523814452)⟩, true⟩

def words05 : List Nat := [360582912587245569, 360582912701923718, 360582912804917945, 360582912805559837, 360582912600842000, 360582912009830807, 360582911418721985, 360582911378299528, 360582911439096001, 360582911500044891]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360567500548355275, 360567514196039604⟩, ⟨719430968272471120, 719862300244088432⟩, true⟩

def words06 : List Nat := [360582911500623275, 360582911196133896, 360582910577700829, 360582910298406465, 360582910018947072, 360582909559984542, 360582908799720682, 360582907626264950, 360582906452736057, 360582905735493188]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360572369889027378, 360572383542757670⟩, ⟨491792284341929680, 492223899114184910⟩, true⟩

def words07 : List Nat := [360582905533864014, 360582905661439659, 360582905662017063, 360582905654925551, 360582905655463618, 360582905633247908, 360582905835900055, 360582905867758863, 360582905868331433, 360582905644064087]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566680561818800, 360566694221621584⟩, ⟨757913361456253790, 758345260329561734⟩, true⟩

def words08 : List Nat := [360582905419670099, 360582905027826428, 360582904921895371, 360582904887497953, 360582904853049931, 360582904428254180, 360582903683681415, 360582902894735397, 360582902105622711, 360582901643299925]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552565926099542, 360552579592024721⟩, ⟨1418444575099195151, 1418876760469147311⟩, true⟩

def words09 : List Nat := [360582901297499079, 360582900723801920, 360582900150006329, 360582900017815086, 360582900018362258, 360582899799323814, 360582899580225770, 360582899077272265, 360582898118609967, 360582897471521926]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk467B
