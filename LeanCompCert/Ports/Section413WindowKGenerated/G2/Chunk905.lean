import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk905

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

def state06 : KState := ⟨⟨360611894635805704, 360611948568973048⟩, ⟨(-2714261134547164483), (-2710962952362477451)⟩, true⟩

def words05 : List Nat := [360582010671375732, 360582010935975824, 360582011295247221, 360582011601437841, 360582011803798105, 360582012006255548, 360582012307404238, 360582012691008597, 360582013022650829, 360582013354561078]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598450745291751, 360598504690895378⟩, ⟨(-1496816668713529119), (-1493517360235291765)⟩, true⟩

def words06 : List Nat := [360582013625138416, 360582013774108397, 360582013941412872, 360582014109090605, 360582014221325650, 360582014336831097, 360582014373478050, 360582014410254873, 360582014489997209, 360582014673558314]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583440157223522, 360583494115166266⟩, ⟨(-137195659470741034), (-133895233377630672)⟩, true⟩

def words07 : List Nat := [360582014893312861, 360582015113308199, 360582015230900183, 360582015379280739, 360582015496405123, 360582015613890792, 360582015816506226, 360582015897657859, 360582015915142512, 360582015932839094]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598640005085017, 360598693975362402⟩, ⟨(-1514036148383460589), (-1510734604958108855)⟩, true⟩

def words08 : List Nat := [360582016050214438, 360582016235215816, 360582016541572554, 360582016848179739, 360582017029825640, 360582017089850697, 360582017146856183, 360582017204226215, 360582017358433165, 360582017543874086]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595173871657791, 360595227854397005⟩, ⟨(-1200035505916341479), (-1196732833514442671)⟩, true⟩

def words09 : List Nat := [360582017668046173, 360582017792361111, 360582017937391652, 360582018177234137, 360582018386075759, 360582018595136450, 360582018708965824, 360582018734377157, 360582018881230513, 360582019028517441]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk905
