import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk346A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556253053342844, 360556260340491324⟩, ⟨877842761141421361, 878013226808135427⟩, true⟩

def state01 : KState := ⟨⟨360640955266204212, 360640962557731267⟩, ⟨(-2053355861060844222), (-2053185243873714522)⟩, true⟩

def words00 : List Nat := [360581635712301334, 360581634953999850, 360581635236051199, 360581635794428513, 360581635794859569, 360581635734633625, 360581636663266029, 360581637591989279, 360581639088777961, 360581640803263794]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360617086150308412, 360617093446248429⟩, ⟨(-1227070460159588556), (-1226899690217945194)⟩, true⟩

def words01 : List Nat := [360581642061218549, 360581643319152552, 360581645410725864, 360581647928836832, 360581649692739008, 360581651456607656, 360581652591657677, 360581653378032858, 360581654402097281, 360581655426254266]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360630565447328639, 360630572747639701⟩, ⟨(-1693710124372355788), (-1693539203083257888)⟩, true⟩

def words02 : List Nat := [360581657062786751, 360581658721263990, 360581659961870775, 360581661202452834, 360581662209642950, 360581663717218602, 360581665725520780, 360581667733798596, 360581668929571333, 360581670342191310]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360650189026612568, 360650196331301927⟩, ⟨(-2373308239087596264), (-2373137166156398602)⟩, true⟩

def words03 : List Nat := [360581672587440225, 360581674832702652, 360581677610096074, 360581679557551638, 360581680794912965, 360581682032247277, 360581683628950751, 360581685773956651, 360581687752122022, 360581689730275502]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360617312680173753, 360617319989293653⟩, ⟨(-1234688183862601438), (-1234516957437162646)⟩, true⟩

def words04 : List Nat := [360581691284341870, 360581692008716994, 360581692605642629, 360581693202663057, 360581693220207367, 360581693220672726, 360581692970523732, 360581692301089797, 360581691793726706, 360581692822474885]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk346A
