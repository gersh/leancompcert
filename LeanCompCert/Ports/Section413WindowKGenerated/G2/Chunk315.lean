import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk315

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

def state06 : KState := ⟨⟨360526900952413527, 360526906969100894⟩, ⟨1761194679032923844, 1761323085999059616⟩, true⟩

def words05 : List Nat := [360582723191437726, 360582721964714561, 360582720737987533, 360582720268286869, 360582720268638307, 360582720031540795, 360582719794404758, 360582718911962627, 360582717453301844, 360582715685387303]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360544255057471881, 360544261078120356⟩, ⟨1213221772400949491, 1213350304399051333⟩, true⟩

def words06 : List Nat := [360582713917446228, 360582712709663251, 360582710910873251, 360582708317402672, 360582705724026176, 360582702657954690, 360582700100705829, 360582698543541580, 360582696986431233, 360582694727293592]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560133752844075, 360560139777453752⟩, ⟨711891183126349364, 712019840199654676⟩, true⟩

def words07 : List Nat := [360582693510261538, 360582693043873904, 360582693110101361, 360582693110521526, 360582692642074166, 360582691312869723, 360582689983676678, 360582688203840280, 360582687034379789, 360582686320841962]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360545907396305329, 360545913424921246⟩, ⟨1160924398046733366, 1161053181656040480⟩, true⟩

def words08 : List Nat := [360582685607295185, 360582684058988309, 360582681509475364, 360582679959184166, 360582678408872079, 360582676607066431, 360582674492714547, 360582671879068917, 360582669265508610, 360582667245169934]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360493006095528375, 360493012128105678⟩, ⟨2832274615808604946, 2832403524578316022⟩, true⟩

def words09 : List Nat := [360582666082088873, 360582664893038887, 360582663704015577, 360582662016107390, 360582659327767067, 360582656176979845, 360582653026269927, 360582650314613042, 360582647987177583, 360582645151035372]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk315
