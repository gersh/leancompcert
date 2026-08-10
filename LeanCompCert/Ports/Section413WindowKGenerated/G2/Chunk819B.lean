import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk819A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk819B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk819A

def state06 : KState := ⟨⟨360595404285416060, 360595448121449637⟩, ⟨(-1080847429934675327), (-1078421002138977439)⟩, true⟩

def words05 : List Nat := [360582288606297508, 360582288700116283, 360582288942485745, 360582289282946081, 360582289553032036, 360582289823322876, 360582289990284383, 360582290064497139, 360582290225989287, 360582290387867336]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591818726202591, 360591862573308266⟩, ⟨(-787044003151254457), (-784616667831056211)⟩, true⟩

def words06 : List Nat := [360582290571739586, 360582290641563029, 360582290642637585, 360582290597753643, 360582290552683181, 360582290412181234, 360582290460173567, 360582290559235541, 360582290574171781, 360582290692181636]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360617490989559346, 360617534847751156⟩, ⟨(-2891517158630976594), (-2889088914526326502)⟩, true⟩

def words07 : List Nat := [360582290958627941, 360582291225436773, 360582291640593243, 360582292005392718, 360582292244740636, 360582292484172698, 360582292709668100, 360582293028601816, 360582293459434505, 360582293890522941]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595532941493241, 360595576810872982⟩, ⟨(-1091412277618058947), (-1088983116271150493)⟩, true⟩

def words08 : List Nat := [360582294246702971, 360582294488483066, 360582294698603040, 360582294909078288, 360582295048443369, 360582295049617978, 360582295040609552, 360582294957217043, 360582294907870618, 360582295071215323]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574281939940936, 360574325820400155⟩, ⟨651014260065630362, 653444329874095360⟩, true⟩

def words09 : List Nat := [360582295122066193, 360582295173117483, 360582295174164242, 360582295143552664, 360582295090147266, 360582294943332744, 360582294796176918, 360582294771214107, 360582294749655238, 360582294653691303]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk819B
