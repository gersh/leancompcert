import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk824A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607993443136223, 360608037769515317⟩, ⟨(-2117154708767663662), (-2114687984305980246)⟩, true⟩

def state01 : KState := ⟨⟨360586058101962943, 360586102439589089⟩, ⟨(-309691872619819134), (-307224221346499958)⟩, true⟩

def words00 : List Nat := [360582374586465084, 360582374634351149, 360582374746976746, 360582374859980781, 360582374935694514, 360582374936875549, 360582374865801737, 360582374701758690, 360582374537494697, 360582374487964349]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569221029598191, 360569265378362471⟩, ⟨1077900628604916747, 1080369197826360387⟩, true⟩

def words01 : List Nat := [360582374501968620, 360582374516190106, 360582374517252328, 360582374457533071, 360582374287325515, 360582374057053741, 360582373826437130, 360582373707354786, 360582373631272072, 360582373473458642]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583039559864760, 360583083919771028⟩, ⟨(-61076916869290767), (-58607429269845213)⟩, true⟩

def words02 : List Nat := [360582373315375284, 360582373384272041, 360582373442112739, 360582373500171755, 360582373501281614, 360582373415509751, 360582373182734424, 360582373067017089, 360582372950956346, 360582372932044690]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564501973601459, 360564546344786497⟩, ⟨1467078831989012809, 1469549249352831021⟩, true⟩

def words03 : List Nat := [360582372933108679, 360582372846929593, 360582372760511105, 360582372646336093, 360582372644051788, 360582372605037069, 360582372565893819, 360582372453068161, 360582372241961260, 360582372027093058]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360562814041178960, 360562858423492811⟩, ⟨1606171344530263279, 1608642679408682861⟩, true⟩

def words04 : List Nat := [360582371811826761, 360582371661767445, 360582371364861546, 360582370994305455, 360582370623572311, 360582370157683964, 360582369812972463, 360582369549005355, 360582369284925610, 360582368947196980]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk824A
