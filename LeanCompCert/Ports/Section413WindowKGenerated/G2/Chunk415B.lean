import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk415A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk415B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk415A

def state06 : KState := ⟨⟨360544811444422086, 360544822116765067⟩, ⟨1562349141030164565, 1562648901909053923⟩, true⟩

def words05 : List Nat := [360582425425744604, 360582425653161144, 360582425653670552, 360582425532108716, 360582425009429881, 360582424339633203, 360582423669703804, 360582423303139017, 360582422850122861, 360582421945973659]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576880388305394, 360576891065978738⟩, ⟨229375834974456531, 229675817410393627⟩, true⟩

def words06 : List Nat := [360582421041743050, 360582420040105035, 360582419331526202, 360582419060462816, 360582418789369990, 360582417945224822, 360582417114303348, 360582416747749412, 360582416381050760, 360582416103684064]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561061145390204, 360561071828459235⟩, ⟨887018961701120186, 887319168460438434⟩, true⟩

def words07 : List Nat := [360582415971286542, 360582415492195003, 360582415013025179, 360582414520853975, 360582414442354384, 360582414217413478, 360582413992421890, 360582413478151986, 360582412388375503, 360582411875800756]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360547744349419437, 360547755037804276⟩, ⟨1440830146000059005, 1441130573817716741⟩, true⟩

def words08 : List Nat := [360582411363041643, 360582411210385158, 360582410870391495, 360582410203417354, 360582409536382424, 360582408722644648, 360582408279268112, 360582407592877730, 360582406906463193, 360582405929216099]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588207140395817, 360588217834117022⟩, ⟨(-242312518876216977), (-242011869092180335)⟩, true⟩

def words09 : List Nat := [360582405096542942, 360582404119517400, 360582403142373332, 360582402741990454, 360582402354424211, 360582401429702382, 360582400504916919, 360582400156843780, 360582400240521381, 360582400380952623]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk415B
