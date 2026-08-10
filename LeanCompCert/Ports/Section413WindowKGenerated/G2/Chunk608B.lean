import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk608A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk608B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk608A

def state06 : KState := ⟨⟨360613509205232154, 360613532812905256⟩, ⟨(-1894542557173841503), (-1893571937749319973)⟩, true⟩

def words05 : List Nat := [360582417705108937, 360582418122902671, 360582418524479611, 360582418657169651, 360582418657955289, 360582418562279530, 360582418486693369, 360582418728981666, 360582419240910809, 360582419753018805]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594483870105313, 360594507485884790⟩, ⟨(-736758932150736194), (-735787819330548078)⟩, true⟩

def words06 : List Nat := [360582420129284517, 360582420236650761, 360582420377410599, 360582420518411299, 360582420519137466, 360582420430534817, 360582420263976761, 360582419962538009, 360582419660945779, 360582419828062009]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567501618760352, 360567525242580920⟩, ⟨905879368863669975, 906850971184588931⟩, true⟩

def words07 : List Nat := [360582420172807974, 360582420517720268, 360582420715423417, 360582420871588264, 360582420954038376, 360582421036721766, 360582421209843011, 360582421210695708, 360582421198780220, 360582420954985398]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617239703597427, 360617263335458879⟩, ⟨(-2122460953104411457), (-2121488861214997599)⟩, true⟩

def words08 : List Nat := [360582420711006263, 360582420621616662, 360582420861120266, 360582421100780109, 360582421101579921, 360582421060506786, 360582421260157795, 360582421495396753, 360582422000018619, 360582422573093095]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602494544759892, 360602518184756856⟩, ⟨(-1224575536257857692), (-1223602948958935256)⟩, true⟩

def words09 : List Nat := [360582423010471549, 360582423447932980, 360582423877627343, 360582424489809817, 360582424974706306, 360582425459730420, 360582425789489383, 360582425850706756, 360582426181319495, 360582426512223418]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk608B
