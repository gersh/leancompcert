import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk667A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk667B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk667A

def state06 : KState := ⟨⟨360561492801528567, 360561521418702362⟩, ⟨1427148747604785862, 1428439269694608244⟩, true⟩

def words05 : List Nat := [360582918232311682, 360582918551802082, 360582918757883401, 360582918758825232, 360582918740883296, 360582918586333956, 360582918460295983, 360582918461238671, 360582918371991213, 360582918052460520]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360617301363100649, 360617329989165159⟩, ⟨(-2298920753064836074), (-2297629637386233190)⟩, true⟩

def words06 : List Nat := [360582917732726135, 360582917582921292, 360582917731369632, 360582917918093616, 360582917918962343, 360582917992378898, 360582918253039137, 360582918513972843, 360582918880839135, 360582919397180821]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604697820540013, 360604726455589456⟩, ⟨(-1457330428592122946), (-1456038712946203854)⟩, true⟩

def words07 : List Nat := [360582919801604820, 360582920206110793, 360582920605617582, 360582921133576107, 360582921602493634, 360582922071552369, 360582922428517167, 360582922612502158, 360582922939766761, 360582923267363072]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563894116803894, 360563922760718613⟩, ⟨1267688536688256929, 1268980844402281225⟩, true⟩

def words08 : List Nat := [360582923524047833, 360582923557103787, 360582923557943336, 360582923477887177, 360582923397681937, 360582923176546963, 360582923067618605, 360582922866210850, 360582922664714450, 360582922324192222]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360610241917275374, 360610270570087439⟩, ⟨(-1828131854053778567), (-1826838952042693777)⟩, true⟩

def words09 : List Nat := [360582922040491141, 360582921980774253, 360582921936434767, 360582922048794023, 360582922049663380, 360582921964941261, 360582922018028770, 360582922270439402, 360582922680607168, 360582923090977206]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk667B
