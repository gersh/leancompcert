import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk683A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk683B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk683A

def state06 : KState := ⟨⟨360604470890785135, 360604500952577541⟩, ⟨(-1482126194315776409), (-1480738068943376179)⟩, true⟩

def words05 : List Nat := [360582839491010954, 360582839453419080, 360582839492892114, 360582839645682466, 360582839646598568, 360582839609091161, 360582839605932559, 360582839749360123, 360582840067011043, 360582840384871636]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593236810442002, 360593266881449003⟩, ⟨(-714129625100138490), (-712740869773226386)⟩, true⟩

def words06 : List Nat := [360582840595605479, 360582840883951700, 360582841342147594, 360582841800624580, 360582842116649871, 360582842219095763, 360582842219960965, 360582842188554865, 360582842156978258, 360582842273504506]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580529819759248, 360580559899870454⟩, ⟨154795327683470503, 156184705509549159⟩, true⟩

def words07 : List Nat := [360582842640300815, 360582843007271537, 360582843245387347, 360582843413967756, 360582843520496747, 360582843627304100, 360582843895941271, 360582844001389759, 360582844002252212, 360582843969854508]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594242262726987, 360594272351972330⟩, ⟨(-783007330146845451), (-781617327684271327)⟩, true⟩

def words08 : List Nat := [360582843937235958, 360582844010610428, 360582844112388295, 360582844214334737, 360582844215226684, 360582844117467547, 360582843891690730, 360582843699148482, 360582843526159779, 360582843694288070]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592587180382266, 360592617278843213⟩, ⟨(-669864896421427630), (-668474263657846346)⟩, true⟩

def words09 : List Nat := [360582843705248292, 360582843716302614, 360582843790002301, 360582843971600409, 360582844098984031, 360582844226521669, 360582844227398168, 360582844188996944, 360582844262175896, 360582844406170916]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk683B
