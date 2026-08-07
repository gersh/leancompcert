import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk747

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485029154114843, 362485112387235520⟩, ⟨6112496090549443, 10311284335745401⟩, true⟩

def state01 : KState := ⟨⟨362477353609116134, 362477436865117833⟩, ⟨579506518455809282, 583707016031209310⟩, true⟩

def words00 : List Nat := [371285250513827260, 371285250516398135, 371285250400967018, 371285250271981608, 371285250141926010, 371285250045137902, 371285249857696091, 371285249850236054, 371285249841945564, 371285249835483664]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 74700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 74700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494757229882839, 362494840509180872⟩, ⟨(-720851086139069632), (-716648847977561290)⟩, true⟩

def words01 : List Nat := [371285249732689957, 371285249672787091, 371285249727415987, 371285249729986222, 371285249609217175, 371285249447415331, 371285249298941093, 371285249301849855, 371285249381416748, 371285249512700933]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 74710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 74700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475930377841143, 362476013680295807⟩, ⟨685923150981411579, 690127119525903763⟩, true⟩

def words02 : List Nat := [371285249643187909, 371285249645758332, 371285249537457935, 371285249523044887, 371285249507409162, 371285249495713289, 371285249244804479, 371285248977567143, 371285248709267873, 371285248621009388]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 74720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 74700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471101681641431, 362471185007270018⟩, ⟨1046882396107480539, 1051088096554882911⟩, true⟩

def words03 : List Nat := [371285248554444837, 371285248612533547, 371285248656431097, 371285248659020935, 371285248573850524, 371285248544873799, 371285248600828608, 371285248603399836, 371285248453159603, 371285248267860798]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 74730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 74700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489874670357390, 362489958018992080⟩, ⟨(-356287802664161034), (-352080382622049380)⟩, true⟩

def words04 : List Nat := [371285248081446164, 371285248047246467, 371285247932429914, 371285247945187343, 371285247947209566, 371285247900167217, 371285247757791275, 371285247778157830, 371285247910856913, 371285247976549544]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 74740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 74700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486780932861548, 362486864304978994⟩, ⟨(-125016025745171247), (-120806850249678797)⟩, true⟩

def words05 : List Nat := [371285248041673415, 371285248107701657, 371285248224755529, 371285248253857799, 371285248336763009, 371285248420646780, 371285248503878414, 371285248506450308, 371285248372737303, 371285248397617540]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475808389701303, 362475891784707246⟩, ⟨695399125835610037, 699610012596902335⟩, true⟩

def words06 : List Nat := [371285248599654556, 371285248609124150, 371285248613903931, 371285248619499490, 371285248663917770, 371285248666759878, 371285248638747411, 371285248630271628, 371285248620893492, 371285248612480376]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501848022571836, 362501931440801957⟩, ⟨(-1251707845973652812), (-1247495222623921610)⟩, true⟩

def words07 : List Nat := [371285248542591934, 371285248599179007, 371285248780988027, 371285248825206719, 371285248839358698, 371285248854345521, 371285248961671858, 371285249009004410, 371285249233835854, 371285249459782395]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477092850531540, 362477176292033690⟩, ⟨599578722517465595, 603793086265019025⟩, true⟩

def words08 : List Nat := [371285249651035129, 371285249653607753, 371285249683801125, 371285249745629127, 371285249860934807, 371285249863507940, 371285249765823843, 371285249650681781, 371285249534491089, 371285249471419504]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465932426412114, 362466015891082556⟩, ⟨1434365044184408619, 1438581140803562405⟩, true⟩

def words09 : List Nat := [371285249390062714, 371285249417717067, 371285249437028849, 371285249439601760, 371285249220657810, 371285249010815800, 371285248799668930, 371285248767897841, 371285248513438880, 371285248259275117]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk747
