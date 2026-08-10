import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk803A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605801716181489, 360605843727545285⟩, ⟨(-1903137527065608093), (-1900859140185755241)⟩, true⟩

def state01 : KState := ⟨⟨360595289398919842, 360595331421211733⟩, ⟨(-1059078984491444054), (-1056799720030013004)⟩, true⟩

def words00 : List Nat := [360582172234649189, 360582172261683394, 360582172410876761, 360582172560425571, 360582172670898512, 360582172672047111, 360582172627835653, 360582172505581178, 360582172414546805, 360582172579707705]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578499896229831, 360578541929353730⟩, ⟨289325414599227396, 291605549033897064⟩, true⟩

def words01 : List Nat := [360582172652908085, 360582172726303742, 360582172727329493, 360582172704379833, 360582172635753854, 360582172528725634, 360582172467859264, 360582172519516274, 360582172520540343, 360582172476527957]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595732683903953, 360595774727871947⟩, ⟨(-1094887155955880491), (-1092606150471763825)⟩, true⟩

def words02 : List Nat := [360582172480229767, 360582172648013824, 360582172922270995, 360582173196741526, 360582173309877705, 360582173311026556, 360582173269319937, 360582173213779238, 360582173255867768, 360582173426375990]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567484932423745, 360567526987348131⟩, ⟨1174441994175447402, 1176723879840215954⟩, true⟩

def words03 : List Nat := [360582173519244670, 360582173612258785, 360582173688662990, 360582173843327382, 360582173958981929, 360582174074820972, 360582174098170550, 360582174099319618, 360582173967943144, 360582173786947835]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586043432438724, 360586085498179133⟩, ⟨(-316639869352226653), (-314357114673540045)⟩, true⟩

def words04 : List Nat := [360582173605568994, 360582173579148048, 360582173515693306, 360582173367729033, 360582173219573204, 360582173033078787, 360582173052068706, 360582173139601112, 360582173149574642, 360582173199456360]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk803A
