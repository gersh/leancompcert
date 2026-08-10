import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk905A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk905B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk905A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk905B
