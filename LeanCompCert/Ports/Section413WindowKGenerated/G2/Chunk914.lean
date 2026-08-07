import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk914

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

def state06 : KState := ⟨⟨360609109444405231, 360609164497259885⟩, ⟨(-2489365923009895745), (-2485965837266461489)⟩, true⟩

def words05 : List Nat := [360581982733314334, 360581982746464195, 360581982878652332, 360581982992603308, 360581982993849564, 360581982993441385, 360581983110470230, 360581983289719084, 360581983587979747, 360581983886537649]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610964613635319, 360611019679091929⟩, ⟨(-2659072596384903212), (-2655671358005050160)⟩, true⟩

def words06 : List Nat := [360581984114355500, 360581984371364013, 360581984747501775, 360581985124020575, 360581985423072833, 360581985725382618, 360581985968041112, 360581986210833834, 360581986427796832, 360581986746708933]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582316022712560, 360582371100617850⟩, ⟨(-38429520690167384), (-35027143569060780)⟩, true⟩

def words07 : List Nat := [360581987063203181, 360581987379941948, 360581987636533014, 360581987773958654, 360581987880605853, 360581987987650985, 360581988134392341, 360581988199880760, 360581988205244194, 360581988210798445]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588441614203180, 360588496704600872⟩, ⟨(-598884284756166283), (-595480764768675439)⟩, true⟩

def words08 : List Nat := [360581988211873061, 360581988274056733, 360581988334644285, 360581988395465068, 360581988396698649, 360581988360032510, 360581988232986117, 360581988124655945, 360581988015939667, 360581988077907879]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598883232963941, 360598938335954556⟩, ⟨(-1554254140508926715), (-1550849468334961535)⟩, true⟩

def words09 : List Nat := [360581988090266582, 360581988102769492, 360581988234350242, 360581988465874913, 360581988643196245, 360581988820728585, 360581988906369409, 360581988973618624, 360581989159926397, 360581989346672090]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk914
