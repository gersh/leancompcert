import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk831A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592247520535214, 360592292632941160⟩, ⟨(-822156981438836919), (-819625212890799899)⟩, true⟩

def state01 : KState := ⟨⟨360593242076776861, 360593287200404218⟩, ⟨(-904801627803878978), (-902268926700944496)⟩, true⟩

def words00 : List Nat := [360582429896724143, 360582430077614452, 360582430185709115, 360582430293952528, 360582430307685965, 360582430408985350, 360582430595499286, 360582430782236820, 360582430877106889, 360582431008965047]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360606815193489834, 360606860328378805⟩, ⟨(-2033025106573012223), (-2030491469461127443)⟩, true⟩

def words01 : List Nat := [360582431105041576, 360582431201448277, 360582431345901303, 360582431414771499, 360582431415881189, 360582431361156722, 360582431394956351, 360582431597858122, 360582431892719219, 360582432187843187]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603793750368246, 360603838896608266⟩, ⟨(-1781938590210957771), (-1779404009545402753)⟩, true⟩

def words02 : List Nat := [360582432399905652, 360582432636505479, 360582432980430511, 360582433324709644, 360582433558392139, 360582433682898137, 360582433693173796, 360582433703571919, 360582433818743366, 360582434077593153]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589110316564772, 360589155474043219⟩, ⟨(-561198861778873774), (-558663346805785626)⟩, true⟩

def words03 : List Nat := [360582434431832508, 360582434786312396, 360582435067819418, 360582435233396835, 360582435318552032, 360582435404016700, 360582435633735592, 360582435841387877, 360582435923292389, 360582436005347801]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599705545338602, 360599750714078192⟩, ⟨(-1442104163418761309), (-1439567712140282475)⟩, true⟩

def words04 : List Nat := [360582436190846226, 360582436463394221, 360582436749041411, 360582437034911471, 360582437184915791, 360582437338324743, 360582437488669045, 360582437639363936, 360582437811914488, 360582438021360844]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk831A
