import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk356A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk356B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk356A

def state06 : KState := ⟨⟨360612698992434139, 360612706752129129⟩, ⟨(-1091779132242455892), (-1091592064700059786)⟩, true⟩

def words05 : List Nat := [360582093684764837, 360582094040213865, 360582094954304993, 360582095085240761, 360582095085681956, 360582094547408770, 360582094100905515, 360582094786111257, 360582095644940054, 360582096503827061]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609178847019256, 360609186611268842⟩, ⟨(-966448672017408734), (-966261442035486370)⟩, true⟩

def words06 : List Nat := [360582096966467749, 360582097309335923, 360582097992012653, 360582098674790376, 360582098814068995, 360582098814549021, 360582098698013007, 360582098186268995, 360582097700096358, 360582098460052575]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360555872574974792, 360555880343739791⟩, ⟨935401170523965348, 935588561593395302⟩, true⟩

def words07 : List Nat := [360582100004294517, 360582101548552132, 360582102410906916, 360582102491072135, 360582102491473420, 360582102354756662, 360582102864908071, 360582102865387019, 360582102730687536, 360582101996250817]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360630590053518575, 360630597826804410⟩, ⟨(-1730946470621955782), (-1730758918227024112)⟩, true⟩

def words08 : List Nat := [360582101261747312, 360582101209995180, 360582101688208099, 360582102166488025, 360582102166935856, 360582101957374353, 360582102189216204, 360582102606143946, 360582103600524504, 360582104959744731]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598484122942364, 360598491900799200⟩, ⟨(-584972655208232733), (-584784939652633217)⟩, true⟩

def words09 : List Nat := [360582105923512611, 360582106887278827, 360582107829232759, 360582109159543127, 360582109882239831, 360582110604972179, 360582110867336564, 360582110910479934, 360582111369719100, 360582111829102256]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk356B
