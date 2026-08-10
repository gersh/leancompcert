import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk185A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk185B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk185A

def state06 : KState := ⟨⟨360749099895191912, 360749101881249997⟩, ⟨(-3039837757760303096), (-3039812808048022668)⟩, true⟩

def words05 : List Nat := [360585252338558776, 360585261811493972, 360585274183417789, 360585283669775413, 360585290685711151, 360585297700909398, 360585303136496384, 360585310038147222, 360585318863330171, 360585327687615602]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360653383168305131, 360653385156615831⟩, ⟨(-1263354057414361201), (-1263329065882419499)⟩, true⟩

def words06 : List Nat := [360585334622727283, 360585338674699644, 360585343935239642, 360585349195287651, 360585353124033247, 360585354170593229, 360585354170805901, 360585353742336034, 360585354511980190, 360585358175522599]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548087289994822, 360548089280536816⟩, ⟨692539353552241669, 692564386530616479⟩, true⟩

def words07 : List Nat := [360585361667068541, 360585365158280363, 360585366759923644, 360585366896474257, 360585366896672676, 360585366261873468, 360585365775454499, 360585366011148580, 360585366011360850, 360585364005323179]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360673312914391390, 360673314907168328⟩, ⟨(-1634881678448694889), (-1634856603934190413)⟩, true⟩

def words08 : List Nat := [360585361999448665, 360585361756853637, 360585365468803188, 360585369180398817, 360585370036424212, 360585370036661072, 360585368886649940, 360585369756811476, 360585372109506143, 360585376840150191]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360668121502920932, 360668123497953840⟩, ⟨(-1538211982837122006), (-1538186866372725690)⟩, true⟩

def words09 : List Nat := [360585380109993404, 360585383379514806, 360585389536522478, 360585397145770943, 360585404009527918, 360585410872585331, 360585416276459369, 360585420832486550, 360585425279061423, 360585429725233410]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk185B
