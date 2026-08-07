import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk728

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593674979352768, 360593709243987329⟩, ⟨(-825595493593675712), (-823910626455981308)⟩, true⟩

def state01 : KState := ⟨⟨360576860013794429, 360576894288276944⟩, ⟨398540682556025122, 400226266674996040⟩, true⟩

def words00 : List Nat := [360582392006742278, 360582392007776583, 360582391980959382, 360582392032520686, 360582392036143294, 360582392037177769, 360582391917427241, 360582391650817917, 360582391384021413, 360582391146767193]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568408102501443, 360568442386726072⟩, ⟨1013995024062828215, 1015681317553406961⟩, true⟩

def words01 : List Nat := [360582391072110945, 360582391062643567, 360582391053068172, 360582390923362935, 360582390801189395, 360582390631672204, 360582390479444617, 360582390480480549, 360582390411816438, 360582390221353282]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590188900650439, 360590223194652131⟩, ⟨(-572219450381553461), (-570532444877505907)⟩, true⟩

def words02 : List Nat := [360582390030668582, 360582389790129201, 360582389721974432, 360582389782621862, 360582389783577223, 360582389682713490, 360582389525508817, 360582389451912016, 360582389437644423, 360582389546276062]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575613180538243, 360575647484382124⟩, ⟨489420581652695236, 491108304013051454⟩, true⟩

def words03 : List Nat := [360582389547204230, 360582389511534827, 360582389591565607, 360582389816077922, 360582389909944892, 360582390003962932, 360582390004893593, 360582390003656010, 360582389864398987, 360582389773014923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591232723354766, 360591267036961452⟩, ⟨(-648367223045290346), (-646678789516051136)⟩, true⟩

def words04 : List Nat := [360582389681291084, 360582389796846675, 360582389823523231, 360582389850311778, 360582389851180296, 360582389802283277, 360582389977710453, 360582390153331791, 360582390182222535, 360582390305145609]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360607250072989325, 360607284396359464⟩, ⟨(-1815373875954131042), (-1813684731107791540)⟩, true⟩

def words05 : List Nat := [360582390582970530, 360582390861096800, 360582391103270924, 360582391208503346, 360582391209466948, 360582391156505215, 360582391162200158, 360582391316985017, 360582391659478237, 360582392002196500]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588171142602923, 360588205475849778⟩, ⟨(-425328655212910253), (-423638790701323629)⟩, true⟩

def words06 : List Nat := [360582392229666924, 360582392393924292, 360582392550165248, 360582392706710747, 360582392714210259, 360582392715245425, 360582392534882971, 360582392244505115, 360582391953937149, 360582391931494667]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556555762854815, 360556590105845665⟩, ⟨1878732796234782256, 1880423370840913984⟩, true⟩

def words07 : List Nat := [360582392200077773, 360582392468851682, 360582392643058076, 360582392676243022, 360582392677116714, 360582392577678153, 360582392477954039, 360582392315510013, 360582392096717287, 360582391743755118]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598525683263857, 360598560036024798⟩, ⟨(-1180262739168716066), (-1178571452469581992)⟩, true⟩

def words08 : List Nat := [360582391390568787, 360582391151624446, 360582391048319695, 360582391091262688, 360582391092218240, 360582390976842510, 360582390834177205, 360582390779310809, 360582390856018707, 360582391078918028]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607166096185422, 360607200458834380⟩, ⟨(-1810155144069855706), (-1808463136586876992)⟩, true⟩

def words09 : List Nat := [360582391145149206, 360582391211461915, 360582391465440122, 360582391814351114, 360582392084841544, 360582392355496144, 360582392476637682, 360582392666069827, 360582393007206197, 360582393348690667]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk728
