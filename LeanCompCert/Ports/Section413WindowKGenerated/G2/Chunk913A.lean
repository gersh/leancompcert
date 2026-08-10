import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk913A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579440646746946, 360579495499684880⟩, ⟨223954444203702155, 227336261568840543⟩, true⟩

def state01 : KState := ⟨⟨360594585303846116, 360594640169240385⟩, ⟨(-1158856081213382395), (-1155473126522286463)⟩, true⟩

def words00 : List Nat := [360581985465409585, 360581985467234274, 360581985618351048, 360581985769717635, 360581985818314455, 360581985819634000, 360581985783304313, 360581985739361853, 360581985769378085, 360581985909331697]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584800844322035, 360584855722276184⟩, ⟨(-265382836403398737), (-261998734808535899)⟩, true⟩

def words01 : List Nat := [360581985958875962, 360581986008561533, 360581986153521810, 360581986375583612, 360581986514340546, 360581986653291276, 360581986721514785, 360581986722834404, 360581986702649679, 360581986735572047]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589277524613490, 360589332415013535⟩, ⟨(-674210289484840771), (-670825051269654487)⟩, true⟩

def words02 : List Nat := [360581986781888504, 360581986893587238, 360581986938270380, 360581986983089112, 360581986984200049, 360581987008051309, 360581987151216534, 360581987294631676, 360581987345747620, 360581987427536450]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599231749251019, 360599286652106908⟩, ⟨(-1583432781199719031), (-1580046405330931515)⟩, true⟩

def words03 : List Nat := [360581987628761442, 360581987830384313, 360581987972932270, 360581987996036657, 360581987997253888, 360581987918366772, 360581987853298741, 360581987944790330, 360581988135245257, 360581988325995623]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583238456892851, 360583293372347792⟩, ⟨(-122648359994356409), (-119260833269651585)⟩, true⟩

def words04 : List Nat := [360581988435565048, 360581988451747406, 360581988465074748, 360581988478780899, 360581988479885450, 360581988463482553, 360581988327281323, 360581988131125896, 360581987934721170, 360581987849329220]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk913A
