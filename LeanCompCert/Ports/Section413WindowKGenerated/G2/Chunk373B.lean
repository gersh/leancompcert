import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk373A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk373B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk373A

def state06 : KState := ⟨⟨360537561587622749, 360537570137392267⟩, ⟨1641777081146606627, 1641992999892256305⟩, true⟩

def words05 : List Nat := [360581523528749366, 360581523889915592, 360581523890364039, 360581523890342580, 360581523590211256, 360581522982103948, 360581522481166817, 360581522481670320, 360581521875405223, 360581520699487885]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360632811133433910, 360632819687956179⟩, ⟨(-1917194536844023314), (-1916978440512328822)⟩, true⟩

def words06 : List Nat := [360581519523519617, 360581519063538463, 360581519752735046, 360581520455463985, 360581520525345306, 360581520938780520, 360581521197922776, 360581521457201400, 360581522431868307, 360581523805038614]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613160278945058, 360613168838270143⟩, ⟨(-1182870824893632032), (-1182654549056882630)⟩, true⟩

def words07 : List Nat := [360581524817369642, 360581525829701552, 360581526600328311, 360581527730458572, 360581528326269619, 360581528922127998, 360581529160641975, 360581529292372214, 360581530139209376, 360581530986177988]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574769496295658, 360574778060362942⟩, ⟨252347894007664615, 252564347131732251⟩, true⟩

def words08 : List Nat := [360581532211459288, 360581532723552461, 360581532737572768, 360581532751646215, 360581532752067905, 360581532862132659, 360581533073701229, 360581533285350112, 360581533285802025, 360581532923886123]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360655409416441142, 360655417985263959⟩, ⟨(-2763247963418080853), (-2763031332461579927)⟩, true⟩

def words09 : List Nat := [360581533106400553, 360581533469699325, 360581534319542494, 360581535194035937, 360581535463745986, 360581535733476317, 360581536717542291, 360581538165819182, 360581540141622950, 360581542117440597]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk373B
