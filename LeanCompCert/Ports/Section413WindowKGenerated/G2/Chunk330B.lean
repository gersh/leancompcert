import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk330A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk330B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk330A

def state06 : KState := ⟨⟨360584654711745462, 360584661339577892⟩, ⟨(-114226562812125643), (-114078405943256823)⟩, true⟩

def words05 : List Nat := [360581204415704258, 360581204620942213, 360581205739366752, 360581207566151278, 360581208779541519, 360581209992927852, 360581210746179235, 360581210746620422, 360581210691585949, 360581210796462341]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562024786474427, 360562031418465879⟩, ⟨633903054004875359, 634051348391795993⟩, true⟩

def words06 : List Nat := [360581210875730046, 360581210876171366, 360581210365736173, 360581209326484060, 360581208287223906, 360581206705310977, 360581205839290977, 360581205542851981, 360581205246375309, 360581204425674582]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607200603633985, 360607207239791217⟩, ⟨(-860220293228831913), (-860071861059259239)⟩, true⟩

def words07 : List Nat := [360581204178918917, 360581204512027463, 360581205757287361, 360581206597203538, 360581206597622258, 360581206572927007, 360581206548151568, 360581206699024868, 360581207485372456, 360581208271771531]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594583602456059, 360594590242823407⟩, ⟨(-442767898168938561), (-442619326707946901)⟩, true⟩

def words08 : List Nat := [360581208599734085, 360581209353892392, 360581211019673381, 360581212685487310, 360581213848080307, 360581214415013357, 360581214415406981, 360581214397818781, 360581214380150653, 360581214420796030]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563344565308910, 360563351209836787⟩, ⟨591216036885093543, 591364746038963203⟩, true⟩

def words09 : List Nat := [360581215736859533, 360581217052927980, 360581217910592308, 360581217911034073, 360581217858087175, 360581217573334497, 360581217413088559, 360581217753168417, 360581217753565779, 360581217214248841]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk330B
