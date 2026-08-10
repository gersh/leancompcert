import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk747A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk747B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk747A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk747B
