import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk391A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360528914587517117, 360528923987054117⟩, ⟨2088710083617699985, 2088958494988994131⟩, true⟩

def state01 : KState := ⟨⟨360565049656825483, 360565059061359222⟩, ⟨675807525825607408, 676056132593644000⟩, true⟩

def words00 : List Nat := [360582348669586762, 360582347754106559, 360582347620782881, 360582347880625220, 360582347881120473, 360582347494466634, 360582346456779435, 360582346071579704, 360582345686252519, 360582345078556708]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567913322912471, 360567922732480546⟩, ⟨563827441025279163, 564076244710970491⟩, true⟩

def words01 : List Nat := [360582344637054465, 360582343868982968, 360582343100849561, 360582343305386279, 360582343460900162, 360582343616505045, 360582343616979738, 360582343247504871, 360582342227383900, 360582341859390336]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360549530033461362, 360549539448019028⟩, ⟨1282899232861319892, 1283148231764013090⟩, true⟩

def words02 : List Nat := [360582341491241787, 360582341082429964, 360582340294463965, 360582338971642814, 360582337648803587, 360582336139412299, 360582334957027313, 360582333872801309, 360582332788572819, 360582331378296667]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609647354468448, 360609656774016773⟩, ⟨(-1069830237191578985), (-1069581042979162949)⟩, true⟩

def words03 : List Nat := [360582330540720669, 360582330214208152, 360582330211893499, 360582330324728914, 360582330325216741, 360582329879186354, 360582329433084878, 360582329017016989, 360582329715650271, 360582330414368855]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581988156671162, 360581997581263248⟩, ⟨12678821871696570, 12928213521355414⟩, true⟩

def words04 : List Nat := [360582330785337502, 360582330785866785, 360582330507113586, 360582330421187920, 360582330335116682, 360582330084198973, 360582329733877314, 360582329057722028, 360582328381502858, 360582327803830844]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk391A
