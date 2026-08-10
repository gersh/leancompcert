import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk620A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk620B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk620A

def state06 : KState := ⟨⟨360622787906056348, 360622812491882953⟩, ⟨(-2494643598179959567), (-2493612859427028827)⟩, true⟩

def words05 : List Nat := [360582629762203314, 360582629757462577, 360582630006366027, 360582630298779099, 360582630353355130, 360582630407975752, 360582630722001458, 360582631165095912, 360582631813259045, 360582632461599409]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619406133153678, 360619430727281789⟩, ⟨(-2284759628600344167), (-2283728374615267093)⟩, true⟩

def words06 : List Nat := [360582632959411171, 360582633666015623, 360582634550030118, 360582635434280264, 360582636252008788, 360582636811368990, 360582637189135295, 360582637566982681, 360582637937910965, 360582638531657178]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587148093160343, 360587172695487000⟩, ⟨(-282247785063441310), (-281216022153446968)⟩, true⟩

def words07 : List Nat := [360582639384541473, 360582640237565128, 360582640880144993, 360582641373202358, 360582641714765787, 360582642056561246, 360582642519190610, 360582642723575915, 360582642797321483, 360582642871190461]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618440804594967, 360618465415154364⟩, ⟨(-2225072900801036447), (-2224040626762174251)⟩, true⟩

def words08 : List Nat := [360582643204216322, 360582643670133525, 360582644116375567, 360582644562765869, 360582644789913522, 360582644871427902, 360582645129857401, 360582645388538372, 360582645787457308, 360582646365263685]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611915241649297, 360611939860505230⟩, ⟨(-1819878550443061109), (-1818845761232395473)⟩, true⟩

def words09 : List Nat := [360582646813406135, 360582647261624330, 360582647864308613, 360582648620455007, 360582649210388859, 360582649800440991, 360582650192162239, 360582650405482756, 360582650877836805, 360582651350477495]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk620B
