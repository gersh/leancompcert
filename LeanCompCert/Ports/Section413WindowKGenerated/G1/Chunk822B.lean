import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk822A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk822B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk822A

def state06 : KState := ⟨⟨362506970394876044, 362507072080101469⟩, ⟨(-1800537174602384176), (-1794889061347118400)⟩, true⟩

def words05 : List Nat := [371285250273163750, 371285250474711057, 371285250808183006, 371285251069099015, 371285251374128261, 371285251680280515, 371285251957260233, 371285252102823466, 371285252370013249, 371285252638794567]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362503133227994685, 362503234938594872⟩, ⟨(-1484856958976725888), (-1479206758261347198)⟩, true⟩

def words06 : List Nat := [371285253053817715, 371285253272757349, 371285253474112808, 371285253676515316, 371285253922988070, 371285254096870725, 371285254417369222, 371285254738994553, 371285255030954861, 371285255252456849]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362515435993578250, 362515537730028255⟩, ⟨(-2497105424578519115), (-2491453097072655475)⟩, true⟩

def words07 : List Nat := [371285255505061449, 371285255759142567, 371285256123389072, 371285256322578791, 371285256500361250, 371285256678999145, 371285256954726586, 371285257178194332, 371285257548145873, 371285257919414959]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362497138432050792, 362497240194175143⟩, ⟨(-991514591559038764), (-985860151434953058)⟩, true⟩

def words08 : List Nat := [371285258289363566, 371285258463129937, 371285258769097886, 371285259076505836, 371285259389864446, 371285259507156393, 371285259603053154, 371285259699928722, 371285259875541463, 371285260024394305]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480267865028120, 362480369652824227⟩, ⟨396905030142483374, 402561582925860846⟩, true⟩

def words09 : List Nat := [371285260247087130, 371285260470949622, 371285260693650973, 371285260757843729, 371285260858331660, 371285260960289003, 371285261127684139, 371285261130535494, 371285261101337293, 371285261045083351]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk822B
