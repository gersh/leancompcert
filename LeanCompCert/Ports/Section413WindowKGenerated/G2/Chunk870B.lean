import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk870A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk870B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk870A

def state06 : KState := ⟨⟨360579039876743618, 360579089569833650⟩, ⟨265336501069241093, 268258069566352299⟩, true⟩

def words05 : List Nat := [360582170852893636, 360582170774998053, 360582170724790914, 360582170853956934, 360582170912277711, 360582170970800139, 360582170971929825, 360582170935873778, 360582170904849235, 360582170870885412]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571706193642938, 360571755898526999⟩, ⟨903784599880767888, 906707195226607092⟩, true⟩

def words06 : List Nat := [360582170836511118, 360582170793133862, 360582170654486410, 360582170449977058, 360582170245275087, 360582169955285122, 360582169766098927, 360582169679955346, 360582169593676990, 360582169441598397]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591661517377615, 360591711234112480⟩, ⟨(-833827788159445587), (-830904160907409427)⟩, true⟩

def words07 : List Nat := [360582169335149683, 360582169348667132, 360582169358247478, 360582169393559063, 360582169394728606, 360582169314773954, 360582169234574572, 360582169273775939, 360582169384366812, 360582169495261211]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578540444546249, 360578590173207707⟩, ⟨308736617030683808, 311661282909528782⟩, true⟩

def words08 : List Nat := [360582169539993423, 360582169541246669, 360582169497678988, 360582169542630542, 360582169554060689, 360582169555313969, 360582169435098360, 360582169185479346, 360582168935625913, 360582168784792385]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576614474092574, 360576664214558865⟩, ⟨476465124471012913, 479390818491567713⟩, true⟩

def words09 : List Nat := [360582168744718254, 360582168709028566, 360582168673213362, 360582168571597910, 360582168473255200, 360582168342097695, 360582168210571976, 360582168188284051, 360582168189400838, 360582168127515141]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk870B
