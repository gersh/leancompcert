import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk767A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk767B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk767A

def state06 : KState := ⟨⟨360584977795088857, 360585016048556726⟩, ⟨(-220124075322850018), (-218140848818656694)⟩, true⟩

def words05 : List Nat := [360582175804128431, 360582175607522826, 360582175410583750, 360582175383322219, 360582175186600303, 360582174811767587, 360582174436734297, 360582174231491905, 360582174191652202, 360582174229809985]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566379279863910, 360566417543776238⟩, ⟨1207573697972941206, 1209557726246157476⟩, true⟩

def words06 : List Nat := [360582174230795477, 360582174184622417, 360582174191435519, 360582174241240057, 360582174242160748, 360582174197665405, 360582174021129776, 360582173759883702, 360582173498456444, 360582173147869584]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559922487039465, 360559960761266029⟩, ⟨1703340534408979891, 1705325354557132705⟩, true⟩

def words07 : List Nat := [360582172943526255, 360582172908790327, 360582172873933194, 360582172736377138, 360582172518977853, 360582172214920719, 360582171910529369, 360582171775731497, 360582171590619736, 360582171302481934]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577656807117646, 360577695091683736⟩, ⟨341620117094560779, 343605731163266173⟩, true⟩

def words08 : List Nat := [360582171014095934, 360582170895396397, 360582170880834537, 360582170860498227, 360582170840077544, 360582170675296453, 360582170341066604, 360582170110725977, 360582169880059904, 360582169707273830]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576648235376460, 360576686530369323⟩, ⟨419036292786034962, 421022707578196270⟩, true⟩

def words09 : List Nat := [360582169649990887, 360582169454569092, 360582169258942183, 360582169164405079, 360582169154623852, 360582169102468663, 360582169050223442, 360582168857084591, 360582168667005512, 360582168596874248]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk767B
