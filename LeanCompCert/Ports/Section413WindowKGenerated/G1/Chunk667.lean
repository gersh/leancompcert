import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk667

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473116617121121, 362473182393336773⟩, ⟨819307916796290855, 822271083526650167⟩, true⟩

def state01 : KState := ⟨⟨362477951778906237, 362478017575519556⟩, ⟨496806427259942755, 499770954618417287⟩, true⟩

def words00 : List Nat := [371285510151972205, 371285510154479208, 371285510083178677, 371285510066504324, 371285510049075554, 371285509996047075, 371285509642961835, 371285509464557360, 371285509284974616, 371285509270237266]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474649374442120, 362474715191790841⟩, ⟨717152781154279724, 720118691876167872⟩, true⟩

def words01 : List Nat := [371285509159638569, 371285509024442289, 371285508974977505, 371285508977485002, 371285508953339946, 371285508938580905, 371285508923110682, 371285508859816152, 371285508496569543, 371285508337652295]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467590847097824, 362467656684722121⟩, ⟨1188170404242389633, 1191137667856389911⟩, true⟩

def words02 : List Nat := [371285508239975288, 371285508242251405, 371285508040830044, 371285507819347631, 371285507596984656, 371285507391001575, 371285507103753079, 371285507009187254, 371285506913840454, 371285506792137922]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485732882271705, 362485798740454842⟩, ⟨(-22561623793975808), (-19592988185110446)⟩, true⟩

def words03 : List Nat := [371285506526215469, 371285506355435417, 371285506234263098, 371285506236539818, 371285506020637153, 371285505768907140, 371285505516238141, 371285505379881047, 371285505166024379, 371285505172959823]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483238242642454, 362483304121365526⟩, ⟨143910853550846908, 146880860096928092⟩, true⟩

def words04 : List Nat := [371285505179331766, 371285505181625447, 371285505067346731, 371285505106204742, 371285505153872781, 371285505156152800, 371285504961236885, 371285504760936035, 371285504581088811, 371285504583689076]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk667
