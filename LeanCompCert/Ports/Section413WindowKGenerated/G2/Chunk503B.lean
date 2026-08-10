import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk503A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk503B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk503A

def state06 : KState := ⟨⟨360606674701535674, 360606690620942394⟩, ⟨(-1245994301179953369), (-1245452589268781643)⟩, true⟩

def words05 : List Nat := [360581960997904935, 360581960727406188, 360581960456714716, 360581960434278752, 360581960285129384, 360581959795970325, 360581959306697931, 360581959139899863, 360581959631555761, 360581960123349639]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580623188599613, 360580639114623472⟩, ⟨66050676158651392, 66592721341557966⟩, true⟩

def words06 : List Nat := [360581960417602293, 360581960639939244, 360581961255645198, 360581961871537589, 360581962212100081, 360581962212795476, 360581962160220231, 360581961869679690, 360581961579022566, 360581961185724159]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360532508550220112, 360532524482802352⟩, ⟨2489893621110162911, 2490435996671557283⟩, true⟩

def words07 : List Nat := [360581961268008521, 360581961376679166, 360581961377305022, 360581961239667289, 360581960813434468, 360581960134765589, 360581959455919805, 360581959170567156, 360581958492214144, 360581957511716040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603673874843073, 360603689813988829⟩, ⟨(-1095759147617374700), (-1095216441354505392)⟩, true⟩

def words08 : List Nat := [360581956531094563, 360581955847237385, 360581955368204862, 360581955282574656, 360581955196893272, 360581954773977061, 360581954582746477, 360581954684231788, 360581955015861400, 360581955447904519]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579098638568621, 360579114584352291⟩, ⟨142657203044795793, 143200243824553439⟩, true⟩

def words09 : List Nat := [360581955580731948, 360581955713620201, 360581955714193294, 360581955980732529, 360581956150009591, 360581956319393755, 360581956320013640, 360581956261124254, 360581955914591506, 360581955859031350]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk503B
