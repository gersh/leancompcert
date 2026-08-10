import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk534A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk534B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk534A

def state06 : KState := ⟨⟨360544321285961336, 360544339313172852⟩, ⟨2014405888024762870, 2015057051061318022⟩, true⟩

def words05 : List Nat := [360582035719957243, 360582035094224488, 360582034468359195, 360582034192156706, 360582034137026417, 360582033994008054, 360582033850910596, 360582033508492086, 360582032816700453, 360582032112481893]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360539128475450953, 360539146509642623⟩, ⟨2291999685425719254, 2292651221655908340⟩, true⟩

def words06 : List Nat := [360582031408029352, 360582030986937084, 360582030216551259, 360582029235393286, 360582028254152702, 360582027013384349, 360582026075863283, 360582025407069962, 360582024738229901, 360582023846872021]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360546566390351410, 360546584431551362⟩, ⟨1894120258670455664, 1894772169668172984⟩, true⟩

def words07 : List Nat := [360582023045595641, 360582022296393387, 360582021547012057, 360582020789097049, 360582019682094759, 360582018258986147, 360582016835788193, 360582015651165845, 360582014640191906, 360582013978478591]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360556678680253056, 360556696728516020⟩, ⟨1353194383782678974, 1353846672545037846⟩, true⟩

def words08 : List Nat := [360582013316669700, 360582012479698808, 360582011851754388, 360582011487208646, 360582011122481410, 360582010585325817, 360582009823211273, 360582008797701781, 360582007772088602, 360582007004689979]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360538606491160706, 360538624546411730⟩, ⟨2320046833535514290, 2320699496124498116⟩, true⟩

def words09 : List Nat := [360582006532121116, 360582006327554272, 360582006122918171, 360582005656837405, 360582005199966752, 360582004547571907, 360582003894976430, 360582003485319413, 360582002917128361, 360582002107086955]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk534B
