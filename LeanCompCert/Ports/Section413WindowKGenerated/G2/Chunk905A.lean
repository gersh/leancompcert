import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk905A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360606175096895961, 360606228955834512⟩, ⟨(-2195663041551930850), (-2192371579289029780)⟩, true⟩

def state01 : KState := ⟨⟨360596937876399492, 360596991747803794⟩, ⟨(-1359761080231846617), (-1356468489758647373)⟩, true⟩

def words00 : List Nat := [360582004317117501, 360582004441718163, 360582004561647112, 360582004681953380, 360582004736569186, 360582004781942916, 360582004783106967, 360582004767275192, 360582004800206543, 360582004967304644]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565521660860635, 360565575544560313⟩, ⟨1483975566554397524, 1487269269943030660⟩, true⟩

def words01 : List Nat := [360582005255874385, 360582005544688280, 360582005766294384, 360582005893241350, 360582005966865306, 360582006040837045, 360582006084791458, 360582006086098226, 360582006008301297, 360582005828143423]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599534496964651, 360599588392996897⟩, ⟨(-1595052017672707614), (-1591757197880996256)⟩, true⟩

def words02 : List Nat := [360582005647691839, 360582005565905479, 360582005667029489, 360582005779344357, 360582005780554571, 360582005773290226, 360582005643938413, 360582005636874324, 360582005742812454, 360582005938391503]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360607796621801632, 360607850530301964⟩, ⟨(-2343095899369120137), (-2339799950781489473)⟩, true⟩

def words03 : List Nat := [360582006041455320, 360582006144633152, 360582006369439356, 360582006664082940, 360582006900487065, 360582007137096944, 360582007306378661, 360582007521402278, 360582007807891278, 360582008094822110]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360605278883161953, 360605332803961839⟩, ⟨(-2115163412614547497), (-2111866350361466967)⟩, true⟩

def words04 : List Nat := [360582008399863788, 360582008664977245, 360582008868782390, 360582009072725696, 360582009177826642, 360582009344469150, 360582009632571545, 360582009920918210, 360582010148268300, 360582010407186967]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk905A
