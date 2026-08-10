import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk992A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592035365492384, 360592100539937279⟩, ⟨(-963292316780422127), (-958926773474869695)⟩, true⟩

def state01 : KState := ⟨⟨360568913987461244, 360568979175629228⟩, ⟨1330406004755724221, 1334772909460454633⟩, true⟩

def words00 : List Nat := [360582434075497925, 360582434076940060, 360582434034719059, 360582434018580734, 360582434002032532, 360582433959964525, 360582433816456505, 360582433614839317, 360582433412958705, 360582433191448808]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558399325183636, 360558464526955603⟩, ⟨2373593385887710105, 2377961640311224657⟩, true⟩

def words01 : List Nat := [360582433057024737, 360582432920385582, 360582432783587739, 360582432596073648, 360582432326787477, 360582432032173428, 360582431737119055, 360582431511949502, 360582431322539927, 360582431082491899]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571699532061478, 360571764747434671⟩, ⟨1053943364489994809, 1058312968493276901⟩, true⟩

def words02 : List Nat := [360582430842110457, 360582430688174798, 360582430610221105, 360582430622865774, 360582430624235177, 360582430540815261, 360582430355856885, 360582430243463653, 360582430130657771, 360582429999560977]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566732829558476, 360566798058679926⟩, ⟨1546827980821442335, 1551198949132244627⟩, true⟩

def words03 : List Nat := [360582429893376687, 360582429702563629, 360582429511452615, 360582429422287379, 360582429402258430, 360582429339174504, 360582429275937090, 360582429151849736, 360582428997986042, 360582428842125435]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583923402028619, 360583988644737135⟩, ⟨(-159228042111396036), (-154855725352719508)⟩, true⟩

def words04 : List Nat := [360582428685788211, 360582428631236907, 360582428612510453, 360582428543004406, 360582428473265489, 360582428350210560, 360582428355212322, 360582428395123557, 360582428396408751, 360582428401259964]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk992A
