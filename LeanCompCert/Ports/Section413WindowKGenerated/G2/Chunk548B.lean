import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk548A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk548B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk548A

def state06 : KState := ⟨⟨360589611500103919, 360589630523672463⟩, ⟨(-432001795766187986), (-431296666836456512)⟩, true⟩

def words05 : List Nat := [360581766752589426, 360581767260460039, 360581767915127575, 360581768238612553, 360581768250157870, 360581768261754522, 360581768323587752, 360581768609586512, 360581768753524058, 360581768897620506]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597590944124000, 360597609974949329⟩, ⟨(-869992847395764247), (-869287320322722231)⟩, true⟩

def words06 : List Nat := [360581768898299845, 360581768876437896, 360581768523182028, 360581768427721470, 360581768332053793, 360581768152945597, 360581767982309606, 360581767645935593, 360581767309421699, 360581767593357547]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564933447240211, 360564952485260474⟩, ⟨922121748081031877, 922827669975347031⟩, true⟩

def words07 : List Nat := [360581768072285359, 360581768551343171, 360581768737872570, 360581768738635334, 360581768594003423, 360581768358663570, 360581768218302413, 360581768219066277, 360581768163860349, 360581767858255652]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609972208387884, 360609991253602643⟩, ⟨(-1549814574775906580), (-1549108258010662754)⟩, true⟩

def words08 : List Nat := [360581767577423111, 360581767769874483, 360581768198525864, 360581768627307722, 360581768773409538, 360581768823574469, 360581768865395663, 360581768907428475, 360581769204018976, 360581769718961069]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582478701734552, 360582497754219004⟩, ⟨(-40492131852586785), (-39785416019004801)⟩, true⟩

def words09 : List Nat := [360581770027518892, 360581770336140374, 360581770755127017, 360581771429818969, 360581772020812796, 360581772611910017, 360581772996679915, 360581773050702647, 360581773064523188, 360581773078602549]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk548B
