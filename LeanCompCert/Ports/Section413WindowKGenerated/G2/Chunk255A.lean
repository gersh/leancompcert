import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk255A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360612742702405483, 360612746558742355⟩, ⟨(-746169742208729889), (-746103220412799749)⟩, true⟩

def state01 : KState := ⟨⟨360583568878678897, 360583572738161266⟩, ⟨(-2190597393171893), (-2123995370998287)⟩, true⟩

def words00 : List Nat := [360583489862563033, 360583490146631680, 360583490146929031, 360583489654361232, 360583489161777878, 360583488333838541, 360583489102673132, 360583489871516351, 360583489871815736, 360583489480140374]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575926396966335, 360575930259598755⟩, ⟨192845924625359592, 192912607020947524⟩, true⟩

def words01 : List Nat := [360583490521506129, 360583491562887546, 360583493494079674, 360583493895764596, 360583493896080777, 360583492844954307, 360583491793847991, 360583490427295263, 360583489826907156, 360583489531033746]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360557208615799396, 360557212481611815⟩, ⟨670510733745881970, 670577497310722376⟩, true⟩

def words02 : List Nat := [360583489235133328, 360583488065494167, 360583487359232152, 360583487771811200, 360583487779889649, 360583487780223528, 360583486260487629, 360583483782107344, 360583481303862331, 360583478736892298]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360504461579042819, 360504465448000227⟩, ⟨2017470785462047541, 2017537629334675839⟩, true⟩

def words03 : List Nat := [360583477708365877, 360583476813217114, 360583475918103355, 360583474262654675, 360583472124683166, 360583469595596967, 360583467066604434, 360583466067229196, 360583463749441512, 360583460656666425]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575883291783435, 360575887163900130⟩, ⟨192975447789597925, 193042372365227763⟩, true⟩

def words04 : List Nat := [360583457564058343, 360583456000702673, 360583455707371857, 360583454824818506, 360583453942309467, 360583451699346867, 360583448498155844, 360583446278737895, 360583444059396501, 360583442638356695]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk255A
