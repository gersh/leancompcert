import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk288

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360669522748634778, 360669527719840551⟩, ⟨(-2500203981581323259), (-2500107150924109241)⟩, true⟩

def state01 : KState := ⟨⟨360658959577016937, 360658964551803166⟩, ⟨(-2196028572652054184), (-2195931638859380694)⟩, true⟩

def words00 : List Nat := [360582725338919241, 360582728022930221, 360582730104289392, 360582732185546318, 360582733424700733, 360582735267810572, 360582738312806264, 360582741357665011, 360582743390740746, 360582746036692293]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360688965419848222, 360688970398231234⟩, ⟨(-3060592973258889167), (-3060495935825160793)⟩, true⟩

def words01 : List Nat := [360582749468864855, 360582752900917578, 360582757534239882, 360582760971295638, 360582763286316621, 360582765601205775, 360582769117188964, 360582773238152975, 360582776923309190, 360582780608292469]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360668319107973212, 360668324089979043⟩, ⟨(-2465887778004614137), (-2465790636143151843)⟩, true⟩

def words02 : List Nat := [360582783527155728, 360582785250335474, 360582786782828793, 360582788315326115, 360582789531983777, 360582791255591860, 360582792366938658, 360582793478246744, 360582795451454518, 360582798418439966]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603987503446165, 360603992489044935⟩, ⟨(-610826646162933233), (-610729400698966949)⟩, true⟩

def words03 : List Nat := [360582801558726029, 360582804698866071, 360582806902108284, 360582808755224410, 360582810086119262, 360582811417026627, 360582813947637724, 360582815283800113, 360582816018439403, 360582816753089214]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360637057249739752, 360637062238934833⟩, ⟨(-1564493997761597693), (-1564396648562392903)⟩, true⟩

def words04 : List Nat := [360582818371847231, 360582821034294403, 360582824895792345, 360582828757095349, 360582831597223534, 360582833243435415, 360582834378898164, 360582835514386853, 360582837051414786, 360582838931300353]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk288
