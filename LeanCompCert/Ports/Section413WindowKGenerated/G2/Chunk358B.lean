import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk358A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk358B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk358A

def state06 : KState := ⟨⟨360543795155423330, 360543803005997512⟩, ⟨1371360947864523350, 1371551265251388840⟩, true⟩

def words05 : List Nat := [360582052221085667, 360582052667817429, 360582052668248753, 360582052553811970, 360582052554215202, 360582052294284117, 360582052132987805, 360582052133469536, 360582051458192396, 360582050392089297]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581486009759895, 360581493864884940⟩, ⟨19484354543292561, 19674835146415829⟩, true⟩

def words06 : List Nat := [360582049325940390, 360582048073216212, 360582047290254329, 360582047283161943, 360582047276036445, 360582046601155479, 360582045410048814, 360582044137770373, 360582042865412555, 360582042368792005]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552373970347427, 360552381830060625⟩, ⟨1063838448173268145, 1064029093375912891⟩, true⟩

def words07 : List Nat := [360582042353933216, 360582041751938308, 360582041149884071, 360582041173170048, 360582041173581053, 360582040736500426, 360582040299391624, 360582039471817661, 360582037870461632, 360582037044480244]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583439368291639, 360583447232548074⟩, ⟨(-50875955192860989), (-50685146955806375)⟩, true⟩

def words08 : List Nat := [360582036218382249, 360582036065382370, 360582036065816247, 360582035805669653, 360582035545458971, 360582035088875504, 360582035210357985, 360582035400322098, 360582035400759032, 360582035035981921]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614214119915213, 360614221988721949⟩, ⟨(-1155740685289246190), (-1155549713718958834)⟩, true⟩

def words09 : List Nat := [360582035413724613, 360582035791591456, 360582035893782355, 360582035894264662, 360582035458831147, 360582034365919171, 360582033272967587, 360582033076895380, 360582033973912533, 360582034870989325]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk358B
