import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk408A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk408B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk408A

def state06 : KState := ⟨⟨360563831095993075, 360563841397567318⟩, ⟨759495538635947283, 759780019745604447⟩, true⟩

def words05 : List Nat := [360582435869806977, 360582435419289125, 360582435115472316, 360582435718560969, 360582436168604567, 360582436618716543, 360582436768583322, 360582436769138313, 360582436566163620, 360582436111706956]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561377900630337, 360561388207425469⟩, ⟨859630392974697513, 859915087435759463⟩, true⟩

def words06 : List Nat := [360582435657083489, 360582435514545338, 360582434775626282, 360582433686616119, 360582432597572011, 360582431118309261, 360582430099480361, 360582429678253837, 360582429256991621, 360582428459136645]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585486219878472, 360585496531918195⟩, ⟨(-125933856164408646), (-125648947331076320)⟩, true⟩

def words07 : List Nat := [360582427944789368, 360582427710256713, 360582427475578032, 360582427226254366, 360582426545030363, 360582425372304344, 360582424199526107, 360582423373189621, 360582422926947257, 360582423002715606]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360539382718176523, 360539393035498623⟩, ⟨1758840422417454922, 1759125547219980938⟩, true⟩

def words08 : List Nat := [360582423003209963, 360582422779203604, 360582421959309715, 360582421736550187, 360582421513658560, 360582420759517332, 360582419409634815, 360582417472882386, 360582415536117766, 360582413958639244]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565768183656783, 360565778506205505⟩, ⟨679837860292063451, 680123198837662287⟩, true⟩

def words09 : List Nat := [360582412907000351, 360582412297858658, 360582411688686456, 360582410724924181, 360582409995714472, 360582409114311884, 360582408232784151, 360582407947883537, 360582407841282416, 360582407435272441]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk408B
