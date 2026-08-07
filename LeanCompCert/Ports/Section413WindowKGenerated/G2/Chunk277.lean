import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk277

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360486718075280622, 360486722658627218⟩, ⟨2655816261245805461, 2655902133394419981⟩, true⟩

def state01 : KState := ⟨⟨360577123220259580, 360577127807051257⟩, ⟨151191947584584373, 151277915178802941⟩, true⟩

def words00 : List Nat := [360582600141085385, 360582597978951896, 360582596602009279, 360582595602683108, 360582594603400573, 360582592491851235, 360582590431588629, 360582589298319323, 360582588165027136, 360582587132752405]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360518466516808654, 360518471107086008⟩, ⟨1776834690165279524, 1776920754364070712⟩, true⟩

def words01 : List Nat := [360582586936071341, 360582586084036028, 360582585231997722, 360582583938061892, 360582583424319419, 360582582193358635, 360582580962445027, 360582579079036064, 360582575899555051, 360582573587402173]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360478411551331614, 360478416145045309⟩, ⟨2887325578939340181, 2887411738410895587⟩, true⟩

def words02 : List Nat := [360582571275282416, 360582569515679612, 360582566869026723, 360582563570680705, 360582560272513116, 360582556643126776, 360582553668513512, 360582550087301656, 360582546506313078, 360582542064209063]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587111144527736, 360587115741687949⟩, ⟨(-127655098586144379), (-127568843525358319)⟩, true⟩

def words03 : List Nat := [360582538309650333, 360582534745303282, 360582531181106513, 360582528912535140, 360582526705356931, 360582523362268694, 360582520019351701, 360582517971799186, 360582517008665726, 360582517174818501]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610907285411961, 360610911886057358⟩, ⟨(-788111579127253675), (-788025227370331357)⟩, true⟩

def words04 : List Nat := [360582517175149675, 360582516341814321, 360582517102532707, 360582518130433682, 360582518587881566, 360582518588247145, 360582517751989994, 360582516263315140, 360582514774671497, 360582515603855984]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360513475987331314, 360513480591417889⟩, ⟨1916294037499159196, 1916380484766123656⟩, true⟩

def words05 : List Nat := [360582517921584400, 360582520239215673, 360582521475617403, 360582521475983003, 360582521419144307, 360582520246405079, 360582519073639620, 360582518661836993, 360582516957074493, 360582514470552116]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360545913118517904, 360545917726061878⟩, ⟨1015719965709061688, 1015806508970759608⟩, true⟩

def words06 : List Nat := [360582511984127628, 360582509200984451, 360582507402383729, 360582506897173332, 360582506391971372, 360582504778804375, 360582501873168939, 360582500260760900, 360582498648365316, 360582497002582252]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580794785925939, 360580799396952511⟩, ⟨46767284148440869, 46853924139226883⟩, true⟩

def words07 : List Nat := [360582495685732875, 360582493718583059, 360582491751504916, 360582491076971464, 360582491061368520, 360582490088894979, 360582489116445167, 360582487416003465, 360582486063591256, 360582486003293016]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585764415580879, 360585769030058830⟩, ⟨(-91483806074524911), (-91397070187354625)⟩, true⟩

def words08 : List Nat := [360582486258814105, 360582486259180432, 360582485910219524, 360582484565425519, 360582483220668157, 360582481546915095, 360582480917593184, 360582480966749802, 360582480967076020, 360582480300967133]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360646605553628314, 360646610171561354⟩, ⟨(-1782517685684672078), (-1782430853763331572)⟩, true⟩

def words09 : List Nat := [360582481710284013, 360582483119610198, 360582485819318757, 360582488152424134, 360582489281818957, 360582490411160376, 360582490629880320, 360582491646702642, 360582493953420667, 360582496260055893]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk277
