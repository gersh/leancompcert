import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk362A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360601759602997858, 360601767609349573⟩, ⟨(-716470674296765293), (-716274744211345569)⟩, true⟩

def state01 : KState := ⟨⟨360592033741363639, 360592041752349702⟩, ⟨(-364631952096371611), (-364435854225155755)⟩, true⟩

def words00 : List Nat := [360581981561217951, 360581981538385594, 360581981256668601, 360581981336928701, 360581981337337946, 360581980981249006, 360581980173051113, 360581978942805962, 360581977712535230, 360581977521750571]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583319492814201, 360583327508389991⟩, ⟨(-49123295767809993), (-48927031679259767)⟩, true⟩

def words01 : List Nat := [360581977765464043, 360581978009253580, 360581978009687227, 360581977869144809, 360581977411229728, 360581976760403700, 360581976219124907, 360581976641009944, 360581976678739799, 360581976716537772]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604664666508669, 360604672686676796⟩, ⟨(-822411893483086365), (-822215463037405767)⟩, true⟩

def words02 : List Nat := [360581977159859794, 360581977986639610, 360581978629033153, 360581979271481637, 360581979271943608, 360581979162355562, 360581978581842193, 360581978254393235, 360581978359287959, 360581978986170672]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563451552111282, 360563459576923544⟩, ⟨671066869522106238, 671263468247175450⟩, true⟩

def words03 : List Nat := [360581979126715102, 360581979267311435, 360581979737852036, 360581980837380812, 360581981744065269, 360581982650779240, 360581983109748379, 360581983110235595, 360581982810128800, 360581982299557297]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567810573981947, 360567818603382833⟩, ⟨513019839238972883, 513216604278535697⟩, true⟩

def words04 : List Nat := [360581982037758725, 360581982038246003, 360581981528642108, 360581980639863825, 360581979751054041, 360581978371823143, 360581977578013468, 360581977301720847, 360581977025389703, 360581976302811207]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk362A
