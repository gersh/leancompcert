import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk551A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588511878160251, 360588531075307864⟩, ⟨(-373094720674358853), (-372380048364890215)⟩, true⟩

def state01 : KState := ⟨⟨360584142321041515, 360584161525483011⟩, ⟨(-132491358193776055), (-131776283955437315)⟩, true⟩

def words00 : List Nat := [360581772940051585, 360581772899048514, 360581772529585999, 360581772489018647, 360581772448234981, 360581772274197778, 360581771882201447, 360581771270375708, 360581770658424426, 360581770418735621]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573345202128344, 360573364413792161⟩, ⟨462557773999177350, 463273246295886012⟩, true⟩

def words01 : List Nat := [360581770454611118, 360581770490621372, 360581770491304027, 360581770362988132, 360581770123076694, 360581769747817669, 360581769372339696, 360581769376956315, 360581769377640508, 360581769225952827]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360609498930546951, 360609518149436855⟩, ⟨(-1530460197235667475), (-1529744326601622117)⟩, true⟩

def words02 : List Nat := [360581769074097332, 360581769035492594, 360581769374104678, 360581769712851265, 360581769740300476, 360581769741067224, 360581769717945533, 360581769871105835, 360581770201489046, 360581770705592165]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587359651990985, 360587378878192583⟩, ⟨(-309808801735683582), (-309092527971745950)⟩, true⟩

def words03 : List Nat := [360581770936610040, 360581771167718777, 360581771497028754, 360581771993421398, 360581772406690891, 360581772820070498, 360581773069217455, 360581773179667897, 360581773281961546, 360581773384495122]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591755330860297, 360591774564282532⟩, ⟨(-552257446974332516), (-551540775028939990)⟩, true⟩

def words04 : List Nat := [360581773716464741, 360581773817935448, 360581773818629523, 360581773663479471, 360581773508210093, 360581773189215796, 360581773437918318, 360581773726763547, 360581773824140111, 360581774006268554]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk551A
