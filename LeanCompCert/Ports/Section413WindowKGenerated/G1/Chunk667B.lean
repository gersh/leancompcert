import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk667A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk667B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk667A

def state06 : KState := ⟨⟨362471940048333146, 362472005947599698⟩, ⟨898207166353963628, 901178544282480668⟩, true⟩

def words05 : List Nat := [371285504743427245, 371285504937127526, 371285505129117332, 371285505131394266, 371285505024362992, 371285504958443365, 371285505028765106, 371285505031044179, 371285504927095092, 371285504727472114]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362499322651305326, 362499388570962292⟩, ⟨(-929966309374790911), (-926993570078961643)⟩, true⟩

def words06 : List Nat := [371285504526821159, 371285504522845420, 371285504512539368, 371285504621081026, 371285504692966909, 371285504695288880, 371285504755462733, 371285504889454159, 371285505184283439, 371285505394582143]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497811370430265, 362497877310839038⟩, ⟨(-829040525546042824), (-826066400549377668)⟩, true⟩

def words07 : List Nat := [371285505605086163, 371285505816314666, 371285506120562943, 371285506329146002, 371285506603083946, 371285506877911218, 371285507152213260, 371285507154491116, 371285507340903617, 371285507529006640]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469638521006489, 362469704481681464⟩, ⟨1052495848155859967, 1055471326635896183⟩, true⟩

def words08 : List Nat := [371285507783695769, 371285507785973663, 371285507742159909, 371285507709871098, 371285507676683133, 371285507672719086, 371285507555641136, 371285507481908839, 371285507407446586, 371285507316336890]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503263497949008, 362503329479252813⟩, ⟨(-1193473571895406980), (-1190496715514743200)⟩, true⟩

def words09 : List Nat := [371285507081280898, 371285507071291321, 371285507190117929, 371285507192551662, 371285507194315228, 371285507163029609, 371285507320891626, 371285507401197895, 371285507669541164, 371285507938923855]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk667B
