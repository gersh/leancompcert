import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk682A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk682B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk682A

def state06 : KState := ⟨⟨360556495680544113, 360556525650975353⟩, ⟨1794359932859524343, 1795741817355400737⟩, true⟩

def words05 : List Nat := [360582832728156272, 360582833217862373, 360582833600086253, 360582833768060836, 360582833768875966, 360582833739913218, 360582833710671164, 360582833670672837, 360582833416239793, 360582833031833182]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589842354423538, 360589872333961453⟩, ⟨(-482053212192306787), (-480670706030819225)⟩, true⟩

def words06 : List Nat := [360582832647219220, 360582832477197082, 360582832429613798, 360582832369326456, 360582832308956558, 360582832034473721, 360582831811161615, 360582831682385986, 360582831601952936, 360582831706080936]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596413877187679, 360596443865928304⟩, ⟨(-930779571326375509), (-929396436849361541)⟩, true⟩

def words07 : List Nat := [360582831706955625, 360582831644352692, 360582831670195264, 360582831867174928, 360582832009613997, 360582832152210053, 360582832153075660, 360582832132417092, 360582832317714997, 360582832518161732]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587194314977170, 360587224312804003⟩, ⟨(-301218380638248790), (-299834625709739284)⟩, true⟩

def words08 : List Nat := [360582832932461655, 360582833132742871, 360582833224103339, 360582833315557868, 360582833316379662, 360582833335831487, 360582833514317806, 360582833692989253, 360582833703725883, 360582833769017710]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589104476115736, 360589134483063198⟩, ⟨(-431645342089573277), (-430260964267621339)⟩, true⟩

def words09 : List Nat := [360582833978603054, 360582834188493793, 360582834526469567, 360582834650492554, 360582834651383682, 360582834582414303, 360582834609203307, 360582834814148311, 360582834907183151, 360582835000416274]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk682B
