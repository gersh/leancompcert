import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk728A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk728B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk728A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk728B
