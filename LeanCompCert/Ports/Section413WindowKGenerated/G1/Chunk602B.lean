import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk602A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk602B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk602A

def state06 : KState := ⟨⟨362517145865433982, 362517199125737002⟩, ⟨(-1929244464090226127), (-1927076540391989233)⟩, true⟩

def words05 : List Nat := [371285217798248386, 371285217967660553, 371285218381377851, 371285218481115300, 371285218551694124, 371285218622950819, 371285218969105753, 371285219226287666, 371285219758370276, 371285220291326820]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489885193879034, 362489938472621854⟩, ⟨(-286417551647674754), (-284248516676490566)⟩, true⟩

def words06 : List Nat := [371285220815480544, 371285221043419690, 371285221383176328, 371285221724000102, 371285222088826217, 371285222090866751, 371285222088624052, 371285222086112090, 371285222218109178, 371285222298729328]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471707943289954, 362471761240395093⟩, ⟨809311886948640874, 811482028711958088⟩, true⟩

def words07 : List Nat := [371285222654040230, 371285223010196019, 371285223341273181, 371285223343313906, 371285223355055035, 371285223405297561, 371285223554959622, 371285223557000471, 371285223339774265, 371285223118774522]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483429293138848, 362483482608510263⟩, ⟨102719163068847054, 104890406016178894⟩, true⟩

def words08 : List Nat := [371285222896846789, 371285222856911749, 371285222748218233, 371285222792590481, 371285222794463419, 371285222796505294, 371285222480883733, 371285222353588084, 371285222370969085, 371285222373081771]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489937823593856, 362489991157578697⟩, ⟨(-289720124283347808), (-287547759040284764)⟩, true⟩

def words09 : List Nat := [371285222345806032, 371285222207365751, 371285222202988454, 371285222236466863, 371285222340773278, 371285222445874917, 371285222546314471, 371285222548392237, 371285222535493979, 371285222617106064]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk602B
