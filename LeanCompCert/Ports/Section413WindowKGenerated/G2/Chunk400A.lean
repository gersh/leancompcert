import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk400A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566362327230767, 360566372182649880⟩, ⟨649972773397480568, 650239215711725324⟩, true⟩

def state01 : KState := ⟨⟨360589147139610200, 360589157000140359⟩, ⟨(-261591705784993465), (-261325059003641075)⟩, true⟩

def words00 : List Nat := [360582627757094746, 360582627222672327, 360582627391840329, 360582627721333483, 360582627721846448, 360582627453977280, 360582626739544200, 360582626120760879, 360582625505977747, 360582625669781117]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604321047044219, 360604330912745795⟩, ⟨(-868759097841375776), (-868492244127733836)⟩, true⟩

def words01 : List Nat := [360582625670263961, 360582625521797686, 360582625847552596, 360582626755392135, 360582627392683312, 360582628030031242, 360582628355180802, 360582628914026156, 360582629456750917, 360582629999621992]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589299546613699, 360589309417417715⟩, ⟨(-267553245847648670), (-267286187907831676)⟩, true⟩

def words02 : List Nat := [360582630913939477, 360582631206783289, 360582631207270750, 360582631185708477, 360582631164059436, 360582631286354944, 360582631773892543, 360582632261507522, 360582632270018940, 360582632437379549]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360626727281392917, 360626737157324024⟩, ⟨(-1766097292081670506), (-1765830028879222282)⟩, true⟩

def words03 : List Nat := [360582633227346331, 360582634017438018, 360582634512888271, 360582634671124584, 360582634671625936, 360582634215825887, 360582633926211486, 360582634405767713, 360582635507673617, 360582636609663396]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585091417708083, 360585101298801271⟩, ⟨(-98989097978248104), (-98721628060537306)⟩, true⟩

def words04 : List Nat := [360582637393077433, 360582637555651950, 360582638008826354, 360582638462136656, 360582638756988831, 360582638757531286, 360582638431613387, 360582637624253467, 360582636816830465, 360582636400844653]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk400A
