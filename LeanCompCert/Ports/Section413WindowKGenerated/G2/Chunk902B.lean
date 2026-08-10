import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk902A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk902B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk902A

def state06 : KState := ⟨⟨360593583826370288, 360593637388997710⟩, ⟨(-1054098216092255587), (-1050833534424505911)⟩, true⟩

def words05 : List Nat := [360581994426421688, 360581994589669530, 360581994794015230, 360581994875999125, 360581994877208599, 360581994835514622, 360581994829403107, 360581994962739170, 360581995092785085, 360581995223118488]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589684021764780, 360589737596800712⟩, ⟨(-702180394221764237), (-698914592500950403)⟩, true⟩

def words06 : List Nat := [360581995290690371, 360581995291993119, 360581995303317284, 360581995371212906, 360581995372322052, 360581995355549279, 360581995325955047, 360581995234874762, 360581995143549016, 360581995192346337]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556016657144863, 360556070244465526⟩, ⟨2337233955665575828, 2340500866390706630⟩, true⟩

def words07 : List Nat := [360581995401795423, 360581995611519724, 360581995759454575, 360581995784967569, 360581995786060683, 360581995741455305, 360581995696476221, 360581995629663892, 360581995440186921, 360581995154372380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588271201162111, 360588324800784925⟩, ⟨(-574844680657526375), (-571576659233317295)⟩, true⟩

def words08 : List Nat := [360581994868267533, 360581994705156982, 360581994632828963, 360581994647013704, 360581994648221186, 360581994558521874, 360581994471623053, 360581994389442197, 360581994345795011, 360581994417255744]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583569322316901, 360583622934365086⟩, ⟨(-150304951415405698), (-147035808044776816)⟩, true⟩

def words09 : List Nat := [360581994426952849, 360581994436791937, 360581994443442029, 360581994526206800, 360581994577813445, 360581994629631687, 360581994630803840, 360581994610801240, 360581994629327896, 360581994648874950]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk902B
