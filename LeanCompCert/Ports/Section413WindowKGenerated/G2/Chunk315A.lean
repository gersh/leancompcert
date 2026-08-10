import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk315A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360515455647732380, 360515461640610263⟩, ⟨2120486132336070588, 2120613788587971450⟩, true⟩

def state01 : KState := ⟨⟨360506986774933886, 360506992771754624⟩, ⟨2387213335536694525, 2387341116008375991⟩, true⟩

def words00 : List Nat := [360582780576494656, 360582778683857981, 360582776374783493, 360582773563668025, 360582770752659991, 360582767688089304, 360582765260478517, 360582762787072696, 360582760313782005, 360582757326372472]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615009091102723, 360615015091879177⟩, ⟨(-1017131465945621878), (-1017003560809662022)⟩, true⟩

def words01 : List Nat := [360582754922327146, 360582753521798065, 360582752121233166, 360582751724019956, 360582751363580248, 360582750016971533, 360582748670368171, 360582748726030734, 360582749750049100, 360582750774097075]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578101667870001, 360578107672645033⟩, ⟨146044516070393581, 146172547261197325⟩, true⟩

def words02 : List Nat := [360582750996424877, 360582750996844247, 360582750214180178, 360582749966592023, 360582749718910568, 360582748824110800, 360582747799895827, 360582746224505638, 360582744649128229, 360582743655748782]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360496402931761727, 360496408940486978⟩, ⟨2722571584578627434, 2722699740339613302⟩, true⟩

def words03 : List Nat := [360582744363934996, 360582745219176522, 360582745429838427, 360582745430257935, 360582744636628291, 360582742901852103, 360582741167060999, 360582739206321747, 360582736970120565, 360582734233459065]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564530181569388, 360564536194258722⟩, ⟨573689655330781746, 573817936139042134⟩, true⟩

def words04 : List Nat := [360582731496875419, 360582729761931943, 360582728836249493, 360582728874322779, 360582728874713280, 360582728060623306, 360582726242913747, 360582725426527810, 360582724610073726, 360582723767511941]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk315A
