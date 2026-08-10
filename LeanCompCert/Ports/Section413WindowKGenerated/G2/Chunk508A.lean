import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk508A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551689471497219, 360551705681816080⟩, ⟨1539400292345477108, 1539956718678691930⟩, true⟩

def state01 : KState := ⟨⟨360584444157581108, 360584460374526532⟩, ⟨(-124625522136942414), (-124068759141635346)⟩, true⟩

def words00 : List Nat := [360582019194296893, 360582018819236252, 360582018745186043, 360582018851962014, 360582018852615504, 360582018634335701, 360582018584418071, 360582018606128196, 360582018606700304, 360582018604847887]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360551953446443491, 360551969670087327⟩, ⟨1526365335453111491, 1526922438826827131⟩, true⟩

def words01 : List Nat := [360582018605473539, 360582018460655095, 360582018315719572, 360582017967421233, 360582017818356309, 360582017572727893, 360582017327035491, 360582016836516148, 360582015959804761, 360582015369395215]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360546854295985811, 360546870526237991⟩, ⟨1785475866067931553, 1786033305310131295⟩, true⟩

def words02 : List Nat := [360582014778756814, 360582014574511420, 360582013984156549, 360582013198365531, 360582012412492885, 360582011432666829, 360582010676474305, 360582009819369306, 360582008962221323, 360582007911744781]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596735052435819, 360596751289313811⟩, ⟨(-750300745560494822), (-749742969494898570)⟩, true⟩

def words03 : List Nat := [360582007221057669, 360582006589536286, 360582005957826695, 360582005712344430, 360582005477118735, 360582004909860318, 360582004342490116, 360582003985870688, 360582004180609769, 360582004471401204]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581599413873487, 360581615657460178⟩, ⟨19099511879816137, 19657629047711797⟩, true⟩

def words04 : List Nat := [360582004472044454, 360582004458603427, 360582004431401949, 360582004475445466, 360582004476033575, 360582004423511210, 360582003985234590, 360582003274261391, 360582002563169488, 360582002238169081]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk508A
