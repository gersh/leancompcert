import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk358A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360536730818526574, 360536738641775488⟩, ⟨1622356196597072182, 1622545534920596780⟩, true⟩

def state01 : KState := ⟨⟨360612591975821818, 360612599803608593⟩, ⟨(-1093779878801098432), (-1093590378000152336)⟩, true⟩

def words00 : List Nat := [360582059877183427, 360582059484147946, 360582060356799414, 360582061229494120, 360582061357597441, 360582061358078397, 360582060709950008, 360582060586206581, 360582061116207783, 360582061969479411]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550564398515058, 360550572230894003⟩, ⟨1127892636911247260, 1128082302179903988⟩, true⟩

def words01 : List Nat := [360582062316010658, 360582062662578728, 360582063513492189, 360582064835677923, 360582065565266802, 360582066294893855, 360582066632339588, 360582066632820745, 360582066194498753, 360582065315823649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360542211004970175, 360542218841878213⟩, ⟨1427119909360316048, 1427309736884461438⟩, true⟩

def words02 : List Nat := [360582064437033443, 360582064173633931, 360582063134565454, 360582061703816910, 360582060273070268, 360582058630137354, 360582057596569438, 360582056676788971, 360582055757009346, 360582054447149898]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360628686635895063, 360628694477352158⟩, ⟨(-1671847785709806368), (-1671657795170248524)⟩, true⟩

def words03 : List Nat := [360582053335775415, 360582053001608145, 360582052667325450, 360582052312822854, 360582052138559992, 360582051304312487, 360582050470017862, 360582050937429683, 360582052239257034, 360582053541129111]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570214025751622, 360570221871789114⟩, ⟨423923684535046572, 424113839258907072⟩, true⟩

def words04 : List Nat := [360582054345434443, 360582054374830928, 360582054973109566, 360582055571496164, 360582055843377370, 360582055843858876, 360582055340933804, 360582054224087024, 360582053107213102, 360582052104404426]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk358A
