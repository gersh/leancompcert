import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk467A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586551895274765, 360586565500422240⟩, ⟨(-170258787072862075), (-169829443059803967)⟩, true⟩

def state01 : KState := ⟨⟨360594810794776067, 360594824406033295⟩, ⟨(-556112348767413541), (-555682719398457357)⟩, true⟩

def words00 : List Nat := [360582928974092169, 360582928821086660, 360582928584275377, 360582928695006830, 360582928695543376, 360582928690589581, 360582928647205241, 360582928375076487, 360582928102839034, 360582928220565237]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360543597644980111, 360543611262280823⟩, ⟨1836300226166065891, 1836730137856717901⟩, true⟩

def words01 : List Nat := [360582928464232624, 360582928708003470, 360582928708575503, 360582928664461975, 360582928162905243, 360582927546111763, 360582926929158739, 360582926232657517, 360582925676263109, 360582924835437003]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596447716562894, 360596461339916669⟩, ⟨(-633117086324157440), (-632686891804249054)⟩, true⟩

def words02 : List Nat := [360582923994502673, 360582923355758875, 360582923130973155, 360582923247418921, 360582923248021201, 360582922927114617, 360582922301740283, 360582922133441843, 360582922137630521, 360582922428020835]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360544540870959841, 360544554500430728⟩, ⟨1792850389984531898, 1793280870387255014⟩, true⟩

def words03 : List Nat := [360582922428592570, 360582922417951777, 360582922551423844, 360582922926267223, 360582923047623543, 360582923169077825, 360582923169655244, 360582923051593139, 360582922476555744, 360582921656408205]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566891593286829, 360566905228802649⟩, ⟨747923898841790900, 748354661813992868⟩, true⟩

def words04 : List Nat := [360582920836081352, 360582920305491814, 360582919318023923, 360582918102222127, 360582916886367650, 360582915555429816, 360582914584985786, 360582914071145799, 360582913557253618, 360582912815151612]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk467A
