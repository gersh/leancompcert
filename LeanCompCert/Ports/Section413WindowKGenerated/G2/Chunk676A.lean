import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk676A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360555287026028821, 360555316397016958⟩, ⟨1862370077008159565, 1863711241012276207⟩, true⟩

def state01 : KState := ⟨⟨360601439338982245, 360601468718978122⟩, ⟨(-1257697573149838555), (-1256355800177208317)⟩, true⟩

def words00 : List Nat := [360582885682873469, 360582885494626598, 360582885546096657, 360582885649588425, 360582885650468818, 360582885599460010, 360582885850489633, 360582886101802688, 360582886321892018, 360582886597723043]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581371069643140, 360581400458741757⟩, ⟨99188928076422752, 100531316529468452⟩, true⟩

def words01 : List Nat := [360582886750590489, 360582886903556915, 360582886965858961, 360582887163801101, 360582887306409946, 360582887449170295, 360582887450034767, 360582887429059458, 360582887189416385, 360582887168539591]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568523890052375, 360568553288142890⟩, ⟨967946138156151153, 969289134685735651⟩, true⟩

def words02 : List Nat := [360582887221270448, 360582887222225347, 360582887078544354, 360582886825582770, 360582886572473791, 360582886257430269, 360582886105047084, 360582885947953946, 360582885790753857, 360582885524349984]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360593594243740322, 360593623650841345⟩, ⟨(-727627662147236685), (-726284056192636479)⟩, true⟩

def words03 : List Nat := [360582885319620978, 360582885327090059, 360582885480782477, 360582885640922805, 360582885641812693, 360582885612970289, 360582885734896248, 360582885996883388, 360582886156411905, 360582886316145042]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573378679679345, 360573408095888341⟩, ⟨639683439276383762, 641027661337513142⟩, true⟩

def words04 : List Nat := [360582886317010765, 360582886307208800, 360582886167356280, 360582885996726235, 360582885825838534, 360582885569489069, 360582885156278894, 360582884633912646, 360582884111362489, 360582883744984240]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk676A
