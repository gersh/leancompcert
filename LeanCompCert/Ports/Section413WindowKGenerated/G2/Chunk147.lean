import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk147

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360548401283813260, 360548402503229885⟩, ⟨451032362614100832, 451044500804014468⟩, true⟩

def state01 : KState := ⟨⟨360425085563318956, 360425086784464307⟩, ⟨2264345870383317870, 2264358033994225304⟩, true⟩

def words00 : List Nat := [360579084603413109, 360579084603596692, 360579080902712750, 360579073972798816, 360579067043798048, 360579057228542961, 360579050460423779, 360579041093873883, 360579031728577683, 360579020029467314]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360641878180864288, 360641879403743623⟩, ⟨(-925896995679978199), (-925884806553400905)⟩, true⟩

def words01 : List Nat := [360579009565796944, 360579002024451020, 360578994484076925, 360578991536228049, 360578988747202215, 360578982165665165, 360578975584986831, 360578975346977081, 360578979620499417, 360578983893482541]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360558549105313682, 360558550329946481⟩, ⟨300918150460133457, 300930365406475943⟩, true⟩

def words02 : List Nat := [360578984612803203, 360578984612987517, 360578987891283489, 360578991823212381, 360578993199333908, 360578993199517870, 360578992147891809, 360578988766765781, 360578985386062540, 360578980089987654]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360457750628253596, 360457751854617435⟩, ⟨1786601354235229934, 1786613594688659700⟩, true⟩

def words03 : List Nat := [360578981898601125, 360578985093670880, 360578986011488253, 360578986011672282, 360578984216610303, 360578979162508168, 360578974109038524, 360578973635625163, 360578968598756443, 360578960375288308]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593223136973168, 360593224365076826⟩, ⟨(-210621078527958858), (-210608812421463034)⟩, true⟩

def words04 : List Nat := [360578952152893412, 360578948596402077, 360578950711108900, 360578952825564067, 360578952825733755, 360578951008428801, 360578946631062134, 360578946729880735, 360578946730032493, 360578946769495411]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360593197451398595, 360593198681257143⟩, ⟨(-210376954867249777), (-210364662867363601)⟩, true⟩

def words05 : List Nat := [360578946769662113, 360578944026872554, 360578943113260586, 360578947232397768, 360578948585905959, 360578949939263645, 360578949939427858, 360578948969598551, 360578946332612785, 360578947298365242]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360677810660191074, 360677811891788613⟩, ⟨(-1459938108418201363), (-1459925790742197883)⟩, true⟩

def words06 : List Nat := [360578950622478982, 360578954114414487, 360578954114581980, 360578953577019804, 360578953039500565, 360578952668664786, 360578958556569329, 360578964443712446, 360578967897637879, 360578974589592269]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360720013452819720, 360720014686156830⟩, ⟨(-2083682501265681357), (-2083670157887315891)⟩, true⟩

def words07 : List Nat := [360578985840916053, 360578997090770193, 360579006466847062, 360579013018961855, 360579015770656380, 360579018521992755, 360579021126244741, 360579026110277769, 360579035649573082, 360579045187619024]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360687594220951944, 360687595456047381⟩, ⟨(-1604787506704030702), (-1604775137328851788)⟩, true⟩

def words08 : List Nat := [360579051771733076, 360579056523814347, 360579065829793435, 360579075134572028, 360579083284576414, 360579086902296125, 360579087722919391, 360579088543450098, 360579091389756166, 360579098725783785]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360628372659243365, 360628373896080822⟩, ⟨(-728719085543398066), (-728706690394964254)⟩, true⟩

def words09 : List Nat := [360579105918193232, 360579113109662967, 360579117991152419, 360579121704942816, 360579122287067249, 360579122869162622, 360579127996064678, 360579133630139482, 360579136957349182, 360579140284136024]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk147
