import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk260A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk260B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk260A

def state06 : KState := ⟨⟨360603610334510721, 360603614369734253⟩, ⟨(-535246683291292320), (-535175549603143958)⟩, true⟩

def words05 : List Nat := [360583078100671729, 360583077116154053, 360583076617135435, 360583077158173585, 360583077158491571, 360583076455846750, 360583076048762019, 360583077297472456, 360583078085819823, 360583078874181391]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360557678657816699, 360557682696298820⟩, ⟨661569331824800290, 661640550447541328⟩, true⟩

def words06 : List Nat := [360583078874491850, 360583078330246811, 360583076800714573, 360583076273956615, 360583075747147039, 360583074409002000, 360583071604145037, 360583068056219337, 360583064508494146, 360583062080665815]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360502446869299399, 360502450910996623⟩, ⟨2101682445379529369, 2101753747836166171⟩, true⟩

def words07 : List Nat := [360583061107471019, 360583060486595911, 360583059865734057, 360583058515239527, 360583055698822692, 360583051795567981, 360583047892512798, 360583045065804363, 360583042718144636, 360583039628321630]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360528002705126991, 360528006750055069⟩, ⟨1435211109061168393, 1435282495794173961⟩, true⟩

def words08 : List Nat := [360583036538660415, 360583033663690848, 360583031992429861, 360583031787763300, 360583031583086149, 360583029972536347, 360583026896998514, 360583024442805271, 360583021988705231, 360583019494240358]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360503975927615953, 360503979975803744⟩, ⟨2062155528833628676, 2062227000628616958⟩, true⟩

def words09 : List Nat := [360583017386054321, 360583014269203610, 360583011152524431, 360583009021877681, 360583007628487961, 360583005340089618, 360583003051823688, 360583000023405541, 360582995531585423, 360582992504563462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk260B
