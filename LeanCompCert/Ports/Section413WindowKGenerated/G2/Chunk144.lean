import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk144

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360475788188912450, 360475789356823185⟩, ⟨1503342513123123131, 1503353901870893143⟩, true⟩

def state01 : KState := ⟨⟨360583151988752233, 360583153158352359⟩, ⟨(-43400440816711026), (-43389027733235754)⟩, true⟩

def words00 : List Nat := [360580181684020145, 360580179222926458, 360580174885272293, 360580168132538952, 360580161380713365, 360580152178089584, 360580146680663929, 360580145967940114, 360580145255297233, 360580142331363723]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360623475271523734, 360623476442819825⟩, ⟨(-624941269116367367), (-624929831585693349)⟩, true⟩

def words01 : List Nat := [360580147322337942, 360580152312671694, 360580155274468735, 360580155274648260, 360580153460214245, 360580147671030369, 360580141882615694, 360580137495051826, 360580138728928830, 360580141734298524]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360527316193378531, 360527317366384862⟩, ⟨761526017325265058, 761537479526015184⟩, true⟩

def words02 : List Nat := [360580141734460242, 360580140564805391, 360580134623403913, 360580133457696672, 360580132292104093, 360580129755235450, 360580122448141985, 360580111285613873, 360580100124598969, 360580091966490615]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360498905843791173, 360498907018490159⟩, ⟨1172019232175775335, 1172030718810263019⟩, true⟩

def words03 : List Nat := [360580089422625175, 360580090535670898, 360580090535831576, 360580088336270104, 360580086316762179, 360580083094984183, 360580081418672523, 360580081418852371, 360580078201821352, 360580072580734638]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592619151274200, 360592620327674474⟩, ⟨(-182183285527173960), (-182171774317812896)⟩, true⟩

def words04 : List Nat := [360580066960388220, 360580061172700329, 360580058431688998, 360580053613789855, 360580048796545118, 360580039915037914, 360580028495950185, 360580021838207131, 360580015181330035, 360580014156868453]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360516529822995852, 360516531001109589⟩, ⟨917863466875352414, 917875002852799982⟩, true⟩

def words05 : List Nat := [360580014157028901, 360580012629961340, 360580012531289107, 360580017618146415, 360580018948770331, 360580020279237633, 360580020279398180, 360580018626477830, 360580012223869819, 360580007833948649]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360479617905430937, 360479619085243507⟩, ⟨1452152027634409610, 1452163588185683362⟩, true⟩

def words06 : List Nat := [360580003806192382, 360580004339807348, 360580004339969373, 360580002474259268, 360580000608778902, 360579995470218245, 360579992716769820, 360579988436766284, 360579984157338340, 360579975933079422]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578943081944754, 360578944263459597⟩, ⟨14080606676922584, 14092191868374730⟩, true⟩

def words07 : List Nat := [360579968998193663, 360579964517193009, 360579960036757351, 360579958146966273, 360579951519956749, 360579940864625214, 360579930210727340, 360579922354051310, 360579917548159287, 360579917481130065]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360522718430225415, 360522719613463042⟩, ⟨827859462175062612, 827871072320691040⟩, true⟩

def words08 : List Nat := [360579917414085850, 360579914958521943, 360579911308494925, 360579907501957254, 360579903695897274, 360579898699085885, 360579888972298270, 360579875593453110, 360579862216420449, 360579853572905464]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360346512314739129, 360346513499676919⟩, ⟨3382211052117556973, 3382222686907256067⟩, true⟩

def words09 : List Nat := [360579849630331521, 360579848438886223, 360579847247585782, 360579843669114024, 360579835364366482, 360579824151147636, 360579812939426161, 360579799951223097, 360579786324298820, 360579770236705006]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk144
