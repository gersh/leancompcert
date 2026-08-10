import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk906A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595173871657791, 360595227854397005⟩, ⟨(-1200035505916341479), (-1196732833514442671)⟩, true⟩

def state01 : KState := ⟨⟨360587692167263079, 360587746162334011⟩, ⟨(-522238344463826857), (-518934554746545775)⟩, true⟩

def words00 : List Nat := [360582019148157646, 360582019176949315, 360582019178125674, 360582019146106410, 360582019113874429, 360582019051399870, 360582019065518937, 360582019082679243, 360582019083844708, 360582019103204915]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601762013269974, 360601816020684429⟩, ⟨(-1797262875472472086), (-1793957967247539372)⟩, true⟩

def words01 : List Nat := [360582019211983061, 360582019321155775, 360582019441050668, 360582019442358953, 360582019440815156, 360582019324199967, 360582019211059382, 360582019309332397, 360582019528848480, 360582019748658657]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581532697618623, 360581586717523236⟩, ⟨36006307653215218, 39312347796590892⟩, true⟩

def words02 : List Nat := [360582019907511796, 360582020069519334, 360582020267908305, 360582020466672600, 360582020611886932, 360582020659997695, 360582020661166591, 360582020625386469, 360582020589382129, 360582020485015199]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565630970988461, 360565685003211395⟩, ⟨1477318038565153471, 1480625195179223081⟩, true⟩

def words03 : List Nat := [360582020598110055, 360582020716239277, 360582020773210296, 360582020774518854, 360582020709867711, 360582020615046659, 360582020525182913, 360582020526491515, 360582020411496450, 360582020232637468]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579743188612127, 360579797233202794⟩, ⟨198115350777030350, 201423628462420770⟩, true⟩

def words04 : List Nat := [360582020053476217, 360582019998746950, 360582019999824764, 360582019961907467, 360582019923884250, 360582019782421935, 360582019556009212, 360582019451568267, 360582019346738986, 360582019225794768]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk906A
