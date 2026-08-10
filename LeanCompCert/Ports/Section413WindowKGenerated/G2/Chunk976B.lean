import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk976A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk976B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk976A

def state06 : KState := ⟨⟨360575771903141170, 360575834993592605⟩, ⟨638674557172294025, 642834968745306179⟩, true⟩

def words05 : List Nat := [360582417362738050, 360582417496947519, 360582417568919443, 360582417570337611, 360582417561149450, 360582417525821162, 360582417490089991, 360582417450266941, 360582417436839584, 360582417370909268]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587915590717910, 360587978694551812⟩, ⟨(-547283361948942052), (-543121643377090422)⟩, true⟩

def words06 : List Nat := [360582417312017905, 360582417387739155, 360582417546709534, 360582417705973374, 360582417763254996, 360582417764673781, 360582417813749543, 360582417878487776, 360582417910413440, 360582417968815646]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589382268949302, 360589445386303903⟩, ⟨(-690539990262726010), (-686376951057079950)⟩, true⟩

def words07 : List Nat := [360582417970101340, 360582417947643668, 360582418005810013, 360582418150833744, 360582418268814988, 360582418387023916, 360582418452589506, 360582418520523505, 360582418593610529, 360582418667176775]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593118133307529, 360593181264008786⟩, ⟨(-1055501220872001720), (-1051336877897648880)⟩, true⟩

def words08 : List Nat := [360582418746514464, 360582418841706994, 360582418884182614, 360582418926812247, 360582418928020154, 360582418931243757, 360582419068964515, 360582419206954418, 360582419292247364, 360582419403879423]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592141723262586, 360592204867376102⟩, ⟨(-960125685761960245), (-955960032479068167)⟩, true⟩

def words09 : List Nat := [360582419507848810, 360582419612252073, 360582419804633039, 360582419892832302, 360582419894159381, 360582419891612173, 360582419970061997, 360582420117373823, 360582420218694899, 360582420320314362]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk976B
