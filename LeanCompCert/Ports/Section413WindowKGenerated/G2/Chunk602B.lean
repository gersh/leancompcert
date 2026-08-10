import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk602A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk602B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk602A

def state06 : KState := ⟨⟨360635707754151009, 360635730880488778⟩, ⟨(-3220084758810721806), (-3219143289265291966)⟩, true⟩

def words05 : List Nat := [360582306575674968, 360582306914367646, 360582307463214419, 360582307830369101, 360582307956038158, 360582308081772617, 360582308482794489, 360582309094813134, 360582309982016358, 360582310869382669]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601435456288288, 360601458590673049⟩, ⟨(-1154792371332307984), (-1153850416838019542)⟩, true⟩

def words06 : List Nat := [360582311596650134, 360582312177044523, 360582312749157428, 360582313321497343, 360582313731530945, 360582313867367504, 360582313868118845, 360582313865465938, 360582313900514406, 360582314219137186]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557385285526486, 360557408427843704⟩, ⟨1500453593717870598, 1501396026341930184⟩, true⟩

def words07 : List Nat := [360582314812800897, 360582315406606639, 360582315822732832, 360582315964665271, 360582316037419541, 360582316110394231, 360582316129089821, 360582316129933489, 360582315874439478, 360582315462122768]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583374064771501, 360583397215047070⟩, ⟨(-66300375100176086), (-65357462706788424)⟩, true⟩

def words08 : List Nat := [360582315049625848, 360582314717922781, 360582314573369194, 360582314555962563, 360582314538476038, 360582314288337175, 360582313866844381, 360582313540782530, 360582313214483879, 360582313181564349]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588904117829615, 360588927276161632⟩, ⟨(-399777106548701636), (-398833708394500074)⟩, true⟩

def words09 : List Nat := [360582313182342706, 360582312928586621, 360582312695263458, 360582312891811636, 360582312975082535, 360582313058487985, 360582313059239733, 360582313007130749, 360582313117504162, 360582313228162520]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk602B
