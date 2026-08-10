import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk288A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk288B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk288A

def state06 : KState := ⟨⟨360613309662800734, 360613314655625966⟩, ⟨(-879376478528968984), (-879279024582151720)⟩, true⟩

def words05 : List Nat := [360582840029209397, 360582841127083825, 360582841914721034, 360582843666573067, 360582844875506964, 360582846084418908, 360582846692630665, 360582846693012147, 360582847606520448, 360582848662604860]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576568045914672, 360576573042335611⟩, ⟨180902873518966431, 181000431256027711⟩, true⟩

def words06 : List Nat := [360582849178983821, 360582849179365200, 360582848503309965, 360582847227841023, 360582845952396200, 360582844008906071, 360582842975740989, 360582843058283767, 360582843058623686, 360582842541166787]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360625910641560544, 360625915641580959⟩, ⟨(-1243978185898204895), (-1243880524226342721)⟩, true⟩

def words07 : List Nat := [360582843304585663, 360582844285207502, 360582845607450371, 360582845738092062, 360582845738452586, 360582844621923927, 360582843505399830, 360582843494187837, 360582844985914368, 360582846477624506]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360633242450410576, 360633247454073541⟩, ⟨(-1455924839356336789), (-1455827072470082999)⟩, true⟩

def words08 : List Nat := [360582847358719499, 360582848281842377, 360582849606718547, 360582850931614062, 360582851771222877, 360582853130182997, 360582853889815004, 360582854649436582, 360582855377744047, 360582857122396892]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360530724105491967, 360530729112750158⟩, ⟨1506595964135887982, 1506693834906385338⟩, true⟩

def words09 : List Nat := [360582859766375443, 360582862410244158, 360582864455313261, 360582865310314172, 360582865859385286, 360582866408526530, 360582866624543847, 360582866624925666, 360582865651157961, 360582863847522006]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk288B
