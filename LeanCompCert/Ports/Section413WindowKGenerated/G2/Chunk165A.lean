import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk165A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360628977882019234, 360628979434854278⟩, ⟨(-759576783170578837), (-759559437390803261)⟩, true⟩

def state01 : KState := ⟨⟨360656448420880692, 360656449975673921⟩, ⟨(-1213151571356589102), (-1213134193256785462)⟩, true⟩

def words00 : List Nat := [360582952939043095, 360582955801556040, 360582956811617750, 360582957821579804, 360582957862104804, 360582960794811598, 360582964887819973, 360582968980371739, 360582971223594700, 360582975674101831]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360688390358129288, 360688391914888879⟩, ⟨(-1741207832517819819), (-1741190421943401917)⟩, true⟩

def words01 : List Nat := [360582978908910461, 360582982143386491, 360582985084910327, 360582986492169677, 360582986492363266, 360582984729787499, 360582983870896284, 360582986598081124, 360582992978716805, 360582999358630578]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624899940593142, 360624901499336430⟩, ⟨(-692537894624108555), (-692520451269433849)⟩, true⟩

def words02 : List Nat := [360583003893480904, 360583007941374068, 360583011200981541, 360583014460257042, 360583016786673289, 360583016786881647, 360583015485707987, 360583011351635962, 360583007218024471, 360583009269509473]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360528399159192571, 360528400719897880⟩, ⟨903457752874440105, 903475228671310241⟩, true⟩

def words03 : List Nat := [360583014162528552, 360583019054995468, 360583021083201877, 360583023250237474, 360583024451582907, 360583025652839052, 360583028475253145, 360583028475461677, 360583027675886950, 360583024373384659]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360524347188171704, 360524348750849411⟩, ⟨970461820480425036, 970479328910528546⟩, true⟩

def words04 : List Nat := [360583021071238098, 360583016064967394, 360583012940963131, 360583012199945857, 360583011459000370, 360583007645105808, 360583000212586067, 360582996423047191, 360582992633902916, 360582987985224670]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk165A
