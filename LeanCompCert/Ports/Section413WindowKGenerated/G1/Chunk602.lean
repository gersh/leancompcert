import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk602

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362508529508504006, 362508582658615801⟩, ⟨(-1409124756214095781), (-1406963469345213181)⟩, true⟩

def state01 : KState := ⟨⟨362485756105132601, 362485809273632257⟩, ⟨(-38114303738107324), (-35951909826355270)⟩, true⟩

def words00 : List Nat := [371285211950980556, 371285212032369075, 371285212192294178, 371285212353234158, 371285212596163844, 371285212598202404, 371285212473373396, 371285212278745188, 371285212162666419, 371285212174932247]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491583183758055, 362491636370590966⟩, ⟨(-388917426697893474), (-386753928846532562)⟩, true⟩

def words01 : List Nat := [371285212386878797, 371285212599626089, 371285212810821333, 371285212927534854, 371285213126591566, 371285213326679207, 371285213801845358, 371285213909934925, 371285214018123309, 371285214127040601]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494758614644015, 362494811819758149⟩, ⟨(-580120606099056088), (-577956007259738198)⟩, true⟩

def words02 : List Nat := [371285214348835996, 371285214434129874, 371285214794681135, 371285215156078961, 371285215448679927, 371285215450719162, 371285215539915429, 371285215706829933, 371285216001483661, 371285216162915996]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483244507505271, 362483297731200617⟩, ⟨113449526809029878, 115615244889654766⟩, true⟩

def words03 : List Nat := [371285216291345349, 371285216420472834, 371285216695531281, 371285216834189002, 371285216988132386, 371285217142824149, 371285217256359798, 371285217258399477, 371285217004280044, 371285216974973686]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478606101267942, 362478659343153720⟩, ⟨392976518696157219, 395143332663437895⟩, true⟩

def words04 : List Nat := [371285217154272878, 371285217203120863, 371285217247981031, 371285217293509237, 371285217421206161, 371285217423474887, 371285217542196833, 371285217673151187, 371285217736602444, 371285217738716599]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk602
