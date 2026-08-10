import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk204A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk204B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk204A

def state06 : KState := ⟨⟨360573489993700760, 360573492428396658⟩, ⟨174798846981946446, 174832557038218846⟩, true⟩

def words05 : List Nat := [360582041310114276, 360582039176968374, 360582037043980980, 360582038225066459, 360582039123082714, 360582040021053985, 360582040021290031, 360582039710575009, 360582037936528789, 360582037519160990]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562775993965518, 360562778431137954⟩, ⟨393752113232315544, 393785873970860484⟩, true⟩

def words06 : List Nat := [360582037101749021, 360582035821966214, 360582033899109054, 360582030490940869, 360582027083062979, 360582023076575643, 360582020323320222, 360582019164219073, 360582018005197262, 360582015650188803]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360653590378388637, 360653592818039942⟩, ⟨(-1465974437792062673), (-1465940626298535937)⟩, true⟩

def words07 : List Nat := [360582014710672540, 360582014110964224, 360582014379363174, 360582014379626284, 360582014093935094, 360582011627250522, 360582009160756688, 360582010190166292, 360582013685624474, 360582017180800621]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360648650648494466, 360648653090652622⟩, ⟨(-1364783922327970028), (-1364750059481683056)⟩, true⟩

def words08 : List Nat := [360582019481541122, 360582023459022758, 360582029809056518, 360582036158549651, 360582041038803150, 360582043544373363, 360582044856699419, 360582046168927377, 360582047426151952, 360582050676935299]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360561688637367564, 360561691082001469⟩, ⟨417591139199999008, 417625052786692942⟩, true⟩

def words09 : List Nat := [360582055337267269, 360582059997194630, 360582062673776852, 360582062976971685, 360582062977191907, 360582062683964866, 360582063832370459, 360582064029091236, 360582064029325593, 360582063035795942]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk204B
