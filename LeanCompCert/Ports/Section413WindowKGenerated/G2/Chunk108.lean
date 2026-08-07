import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk108

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360703511672367186, 360703512311765918⟩, ⟨(-1283499281246166047), (-1283494601089024275)⟩, true⟩

def state01 : KState := ⟨⟨360719842116588922, 360719842757225178⟩, ⟨(-1460378881939424849), (-1460374188410729163)⟩, true⟩

def words00 : List Nat := [360584691887644234, 360584701434995288, 360584705531453845, 360584709627168074, 360584711504537635, 360584717659753728, 360584729229298176, 360584740796729081, 360584748012555297, 360584760508736535]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360732508659813540, 360732509301690328⟩, ⟨(-1597725412193696971), (-1597720705248613343)⟩, true⟩

def words01 : List Nat := [360584776381448140, 360584792251262198, 360584809246067436, 360584817797788998, 360584818129424266, 360584818461007210, 360584822992150727, 360584832001766684, 360584845650422271, 360584859296584644]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599327921726850, 360599328564858155⟩, ⟨(-156052354971149057), (-156047634445977465)⟩, true⟩

def words02 : List Nat := [360584868640407977, 360584878332109531, 360584893452564051, 360584908570264076, 360584921286278429, 360584925578299723, 360584925578418128, 360584925513006221, 360584925447583991, 360584921064678488]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360430974879598728, 360430975523969152⟩, ⟨1668480240315064687, 1668484974266187125⟩, true⟩

def words03 : List Nat := [360584930871000830, 360584940675537752, 360584944734932027, 360584944735063700, 360584940381322696, 360584930401255581, 360584920422988404, 360584918917222614, 360584909002407150, 360584894802037989]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360703992904966167, 360703993550582796⟩, ⟨(-1292749566233139058), (-1292744818767099314)⟩, true⟩

def words04 : List Nat := [360584880604259165, 360584870995595079, 360584866873385105, 360584862452251634, 360584858031924224, 360584846325429787, 360584840522461086, 360584841847743723, 360584846562539103, 360584857542955195]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360705363749070506, 360705364395942805⟩, ⟨(-1307620767625743107), (-1307616006529422287)⟩, true⟩

def words05 : List Nat := [360584864253125542, 360584870962073747, 360584886111850937, 360584906281014387, 360584921508400691, 360584936733003078, 360584944022861920, 360584946677062413, 360584957765357131, 360584968851653198]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360701853938804273, 360701854586920550⟩, ⟨(-1269695178783123317), (-1269690404170904663)⟩, true⟩

def words06 : List Nat := [360584988368927881, 360584999505573286, 360585004323136700, 360585009139828567, 360585009257162622, 360585013623053199, 360585026414659087, 360585039203938017, 360585047741873955, 360585058486822040]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360688315937652754, 360688316587018666⟩, ⟨(-1122659333199651371), (-1122654544997787403)⟩, true⟩

def words07 : List Nat := [360585068944223307, 360585079399738842, 360585095414430181, 360585103069428711, 360585103338651217, 360585103607834384, 360585109163253685, 360585121941585718, 360585131426495705, 360585140909691418]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596906701455464, 360596907352082113⟩, ⟨(-128614231911730227), (-128609429986899135)⟩, true⟩

def words08 : List Nat := [360585144813936744, 360585144814069055, 360585144325736637, 360585148280903158, 360585148281015908, 360585146277250196, 360585135929275639, 360585120314461053, 360585104702489365, 360585098571438747]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360462450805417471, 360462451457292485⟩, ⟨1337032788253332259, 1337037603779218349⟩, true⟩

def words09 : List Nat := [360585108047820904, 360585117522490528, 360585122763357722, 360585125938756932, 360585126914877538, 360585127890853709, 360585131464951209, 360585131465083726, 360585126712112575, 360585115457639203]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk108
