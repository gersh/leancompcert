import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk110

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362598251029882963, 362598252566485192⟩, ⟨(-1230362203086027704), (-1230350761223761322)⟩, true⟩

def state01 : KState := ⟨⟨362517814157386555, 362517815696909158⟩, ⟨(-345399314453151681), (-345387840451702943)⟩, true⟩

def words00 : List Nat := [371286422734201132, 371286422734525019, 371286429146553797, 371286436475638226, 371286445695443386, 371286445695767456, 371286443934301527, 371286442153991323, 371286445320477342, 371286448169849700]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362414959055653831, 362414960598098585⟩, ⟨787532957952286941, 787544464141311087⟩, true⟩

def words01 : List Nat := [371286451203067033, 371286454235855162, 371286457249648322, 371286457249972633, 371286449301260969, 371286443783258287, 371286438572732418, 371286438573062342, 371286432098248686, 371286425612993441]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362510083646611459, 362510085191961677⟩, ⟨(-260911973431716335), (-260900435209569517)⟩, true⟩

def words02 : List Nat := [371286419448000977, 371286419448360599, 371286421439001795, 371286425872126501, 371286428268400774, 371286428268725717, 371286422792830789, 371286424157598770, 371286431480364556, 371286433624994986]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362408479882826782, 362408481431146475⟩, ⟨860531565356319078, 860543136346491148⟩, true⟩

def words03 : List Nat := [371286435765441439, 371286437905617641, 371286441198534895, 371286441198895843, 371286442114653930, 371286443785646025, 371286445467609774, 371286445467934933, 371286436239721150, 371286429179003948]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362402718257000799, 362402719808218992⟩, ⟨924142659311729525, 924154262316450467⟩, true⟩

def words04 : List Nat := [371286422119380383, 371286421791330451, 371286410561464233, 371286399246409165, 371286387933280083, 371286378672034599, 371286366480566201, 371286362463850056, 371286358447749403, 371286353678111884]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362506944765559676, 362506946319721451⟩, ⟨(-228279894252516431), (-228268258706176413)⟩, true⟩

def words05 : List Nat := [371286346110342360, 371286345022945505, 371286346216536377, 371286346216861950, 371286337619640793, 371286326245246399, 371286314872773939, 371286311658121140, 371286307236287293, 371286309102588627]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362408833135594821, 362408834692699128⟩, ⟨856882781563723883, 856894449669640257⟩, true⟩

def words06 : List Nat := [371286310929705749, 371286310930031700, 371286301893091035, 371286295297958596, 371286288703855773, 371286284533287467, 371286273170393463, 371286259931048859, 371286246693967775, 371286241598721680]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362389573365617066, 362389574925662328⟩, ⟨1070707028350291376, 1070718729027719292⟩, true⟩

def words07 : List Nat := [371286235754306053, 371286236901681525, 371286238051163686, 371286238051495613, 371286232926543939, 371286230346830549, 371286227767419210, 371286227599015716, 371286218912027502, 371286210190015011]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362454183905726290, 362454185468702447⟩, ⟨354659958894283211, 354671692060749747⟩, true⟩

def words08 : List Nat := [371286201469433805, 371286196121327126, 371286186719557065, 371286185441840688, 371286184164255885, 371286181607185698, 371286170472003116, 371286167458699252, 371286166684961442, 371286166685299449]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362452337947410050, 362452339513356539⟩, ⟨375397243856026878, 375409009978658788⟩, true⟩

def words09 : List Nat := [371286163802015587, 371286160913113235, 371286163247115878, 371286164751591756, 371286166654533485, 371286168557256299, 371286170285756793, 371286170286084033, 371286163191663616, 371286160144886148]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk110
