import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk473A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602406382135387, 360602420353850502⟩, ⟨(-926424192428022487), (-925977619507459937)⟩, true⟩

def state01 : KState := ⟨⟨360624083534112005, 360624097512012513⟩, ⟨(-1952053143473322205), (-1951606277953182977)⟩, true⟩

def words00 : List Nat := [360582844266042272, 360582844266692502, 360582844501618686, 360582844842202710, 360582845071032473, 360582845421750579, 360582845485248856, 360582845548812830, 360582846057497562, 360582846930161502]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575991781509513, 360576005765540961⟩, ⟨323357081710939977, 323804237316577419⟩, true⟩

def words01 : List Nat := [360582847553690322, 360582848177311664, 360582848457902679, 360582848489008523, 360582848489552694, 360582848409277543, 360582848692931024, 360582848771043074, 360582848771622311, 360582848627698962]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585828591397422, 360585842581564249⟩, ⟨(-142041863752597937), (-141594417790239165)⟩, true⟩

def words02 : List Nat := [360582848662023545, 360582849186743580, 360582849965759393, 360582850744866621, 360582851145080873, 360582851145731281, 360582851100489896, 360582851045121692, 360582850989564100, 360582851002730288]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567888682094465, 360567902678459348⟩, ⟨707106307741304625, 707554047087920881⟩, true⟩

def words03 : List Nat := [360582851003315557, 360582850845193766, 360582850686960127, 360582850415321254, 360582850415865641, 360582850351874819, 360582850287815894, 360582849973178193, 360582849213275270, 360582848898296440]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360545631588044198, 360545645590544712⟩, ⟨1760744871024302307, 1761192900862317235⟩, true⟩

def words04 : List Nat := [360582848583117477, 360582848257848785, 360582847487406560, 360582846444936277, 360582845402401009, 360582844085253309, 360582843055634603, 360582842377243057, 360582841698801742, 360582840794364402]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk473A
