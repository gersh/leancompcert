import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk661A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568637897643155, 360568665929599897⟩, ⟨942560416532786381, 943812062349004191⟩, true⟩

def state01 : KState := ⟨⟨360599422468003575, 360599450508769647⟩, ⟨(-1092548178508193224), (-1091295950352225566)⟩, true⟩

def words00 : List Nat := [360582944262955795, 360582943947771606, 360582943832094109, 360582943889065572, 360582943889937292, 360582943758603046, 360582943398770128, 360582943267726862, 360582943232796942, 360582943483458395]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591087661403779, 360591115711037993⟩, ⟨(-541512479741992017), (-540259665268588591)⟩, true⟩

def words01 : List Nat := [360582943619470758, 360582943755580569, 360582943969162859, 360582944298025637, 360582944469512207, 360582944641131995, 360582944698186899, 360582944699123441, 360582944813642753, 360582944938283973]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593199262076513, 360593227320498960⟩, ⟨(-681174579080854089), (-679921183486414639)⟩, true⟩

def words02 : List Nat := [360582945097788372, 360582945263842914, 360582945293529036, 360582945323306755, 360582945324089010, 360582945279418793, 360582945496831681, 360582945714416419, 360582945735023757, 360582945891464371]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611191527777544, 360611219594999394⟩, ⟨(-1871135160193378821), (-1869881182650626231)⟩, true⟩

def words03 : List Nat := [360582946115508439, 360582946339832206, 360582946700670825, 360582946919315733, 360582946943241228, 360582946967254715, 360582947219321936, 360582947602733589, 360582948030946077, 360582948459355080]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573573228789604, 360573601304917081⟩, ⟨616967138906947239, 618221705509209073⟩, true⟩

def words04 : List Nat := [360582948772662405, 360582948857961185, 360582948858733470, 360582948823920666, 360582948788856753, 360582948696635658, 360582948376238865, 360582947896422213, 360582947416440910, 360582947060102406]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk661A
