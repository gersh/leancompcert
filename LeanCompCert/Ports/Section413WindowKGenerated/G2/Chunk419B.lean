import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk419A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk419B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk419A

def state06 : KState := ⟨⟨360656903115727139, 360656914003019279⟩, ⟨(-3122327071835113245), (-3122018334620620633)⟩, true⟩

def words05 : List Nat := [360582503856441718, 360582504007858508, 360582504726234111, 360582505360718205, 360582505514915836, 360582505669152208, 360582506390341708, 360582507597271325, 360582509371002845, 360582511144778994]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619177469523357, 360619188362246880⟩, ⟨(-1539421698874451800), (-1539112733731737544)⟩, true⟩

def words06 : List Nat := [360582512594442440, 360582513479245810, 360582514662187371, 360582515845242276, 360582516511384326, 360582516612776561, 360582516613290010, 360582516428892494, 360582516626219951, 360582517500610709]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550148201578115, 360550159099689601⟩, ⟨1358165929605417035, 1358475120907605173⟩, true⟩

def words07 : List Nat := [360582518496917776, 360582519493295336, 360582520087504074, 360582520343992161, 360582520344471464, 360582520259878028, 360582520253722253, 360582520254293419, 360582519925247443, 360582519154975633]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360631173162738032, 360631184066239893⟩, ⟨(-2043671451685824230), (-2043362034069031946)⟩, true⟩

def words08 : List Nat := [360582518384611315, 360582518258487198, 360582518902954699, 360582519547501037, 360582519704493834, 360582519875894387, 360582520097937024, 360582520320133238, 360582521002197760, 360582522161687274]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360636871273268520, 360636882182216246⟩, ⟨(-2283094130280857585), (-2282784483965034091)⟩, true⟩

def words09 : List Nat := [360582523036765263, 360582523911864484, 360582524759611368, 360582525897279539, 360582526741799419, 360582527586372026, 360582528146719511, 360582528875441678, 360582530170030031, 360582531464757971]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk419B
