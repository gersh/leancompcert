import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk914A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594013476395885, 360594068454235949⟩, ⟨(-1107770726968995175), (-1104377499804140197)⟩, true⟩

def state01 : KState := ⟨⟨360583487830052178, 360583542820471973⟩, ⟨(-145750626085226596), (-142356249071137234)⟩, true⟩

def words00 : List Nat := [360581985754924920, 360581985773912090, 360581985791933053, 360581985810350100, 360581985811455455, 360581985781758861, 360581985754948564, 360581985668230469, 360581985581265095, 360581985499700172]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566441721320401, 360566496724185827⟩, ⟨1412561570647930851, 1415957085380001323⟩, true⟩

def words01 : List Nat := [360581985637345717, 360581985775241589, 360581985819474524, 360581985820795538, 360581985745457044, 360581985623251884, 360581985500654366, 360581985475765375, 360581985374883928, 360581985206852421]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575716569943402, 360575771585278505⟩, ⟨564623171082333627, 568019825852405735⟩, true⟩

def words02 : List Nat := [360581985038508201, 360581984888905792, 360581984827407980, 360581984857202625, 360581984858424546, 360581984775945929, 360581984653310162, 360581984494095308, 360581984334497735, 360581984205051582]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579806641173902, 360579861669093390⟩, ⟨190662015190941592, 194059820614051492⟩, true⟩

def words03 : List Nat := [360581984138290929, 360581984012085862, 360581983885621243, 360581983964158150, 360581984020402258, 360581984076860837, 360581984078038950, 360581984061894221, 360581983954786295, 360581983933098356]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574093862817767, 360574148903201625⟩, ⟨713011485324343686, 716410430551195914⟩, true⟩

def words04 : List Nat := [360581983910975898, 360581983886456930, 360581983827063381, 360581983654280197, 360581983481285129, 360581983278714176, 360581983135692332, 360581983045652049, 360581982955456629, 360581982806214761]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk914A
