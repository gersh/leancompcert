import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk940A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk940B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk940A

def state06 : KState := ⟨⟨360582342956234706, 360582401311139515⟩, ⟨(-35227316099105518), (-31520911029320022)⟩, true⟩

def words05 : List Nat := [360582065344131439, 360582065530324867, 360582065656201311, 360582065785451256, 360582065851739298, 360582065918381868, 360582066097579035, 360582066189983028, 360582066194791900, 360582066199764670]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606451525746375, 360606509893509950⟩, ⟨(-2303038736582884089), (-2299331121954128371)⟩, true⟩

def words06 : List Nat := [360582066200876083, 360582066207742021, 360582066358916223, 360582066510348447, 360582066565687727, 360582066623772307, 360582066774103893, 360582066924855421, 360582067124775966, 360582067386021414]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600614360386151, 360600672741135405⟩, ⟨(-1753950466128304856), (-1750241629871243562)⟩, true⟩

def words07 : List Nat := [360582067590404046, 360582067794940416, 360582067973594646, 360582068208844504, 360582068389821763, 360582068571017040, 360582068695678930, 360582068781885607, 360582068980732827, 360582069180056428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583934948622869, 360583993342192470⟩, ⟨(-184705570632978248), (-180995528171513156)⟩, true⟩

def words08 : List Nat := [360582069412543209, 360582069532688898, 360582069567964103, 360582069603379692, 360582069604520581, 360582069635635958, 360582069677547478, 360582069719703101, 360582069720916936, 360582069720080138]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360616615269647464, 360616673676079173⟩, ⟨(-3259792566513886572), (-3256081313794381350)⟩, true⟩

def words09 : List Nat := [360582069807196564, 360582069894710892, 360582070035351573, 360582070266670721, 360582070382179029, 360582070497774030, 360582070697568441, 360582070953942646, 360582071322766820, 360582071691894155]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk940B
