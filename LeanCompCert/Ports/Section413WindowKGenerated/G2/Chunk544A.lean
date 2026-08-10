import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk544A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360508622052878560, 360508640746009239⟩, ⟨3977928232736904765, 3978615309754472019⟩, true⟩

def state01 : KState := ⟨⟨360570476714628530, 360570495414890095⟩, ⟨612746693639532473, 613434158612793291⟩, true⟩

def words00 : List Nat := [360581775713068657, 360581774706694851, 360581773869726895, 360581773370072824, 360581772870375336, 360581772090163534, 360581771258613940, 360581770628666578, 360581769998520860, 360581769705619976]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590709001624187, 360590727709095901⟩, ⟨(-488275840750024708), (-487587983437226448)⟩, true⟩

def words01 : List Nat := [360581769499098948, 360581769030456874, 360581768561687215, 360581768466865996, 360581768467498659, 360581768419952586, 360581768372330639, 360581767994897100, 360581767987847310, 360581768153346518]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585167311110226, 360585186025691981⟩, ⟨(-186688223101065980), (-185999978823072552)⟩, true⟩

def words02 : List Nat := [360581768655517913, 360581768821074777, 360581768821754603, 360581768817467952, 360581768813069964, 360581768570515637, 360581768669135949, 360581768815015777, 360581768815689387, 360581768855718564]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590942961485013, 360590961683217875⟩, ⟨(-501102052573586586), (-500413419026291258)⟩, true⟩

def words03 : List Nat := [360581768898681961, 360581768941885432, 360581769166825957, 360581769280017394, 360581769280716224, 360581769115172498, 360581769119914980, 360581769495709784, 360581769665186240, 360581769834812698]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607185442937791, 360607204171878985⟩, ⟨(-1385621037987993923), (-1384932011985081241)⟩, true⟩

def words04 : List Nat := [360581769835493744, 360581769785615810, 360581769535191344, 360581769578840337, 360581769579473377, 360581769538298757, 360581769505991355, 360581769305314668, 360581769239652080, 360581769707645361]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk544A
