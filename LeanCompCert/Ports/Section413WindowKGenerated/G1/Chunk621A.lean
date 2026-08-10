import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk621A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498232582959833, 362498289280336501⟩, ⟨(-802812133129406344), (-800433911829788866)⟩, true⟩

def state01 : KState := ⟨⟨362484247510129019, 362484304226259226⟩, ⟨65724241508513323, 68103627502462005⟩, true⟩

def words00 : List Nat := [371285400369059576, 371285400371166676, 371285400341785818, 371285400297478172, 371285400283807043, 371285400286144504, 371285400400227503, 371285400575637184, 371285400724279186, 371285400726460522]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503561706714768, 362503618441951664⟩, ⟨(-1134015128632615180), (-1131634555828298536)⟩, true⟩

def words01 : List Nat := [371285400766860937, 371285400826007853, 371285401114097753, 371285401155770607, 371285401157402220, 371285401127759665, 371285401196902116, 371285401233160395, 371285401527848449, 371285401823484024]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483038803867961, 362483095558108818⟩, ⟨140897590353361487, 143279343780354307⟩, true⟩

def words02 : List Nat := [371285402117203179, 371285402119311169, 371285402201264472, 371285402305957473, 371285402415536459, 371285402417644453, 371285402181941802, 371285401928403342, 371285401677440391, 371285401679850012]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469731588619481, 362469788361847697⟩, ⟨967839969494437288, 970222902703298822⟩, true⟩

def words03 : List Nat := [371285401866362798, 371285402090864287, 371285402305168557, 371285402307277636, 371285402223868466, 371285402152946952, 371285402266696551, 371285402268805012, 371285402110959656, 371285401862052128]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498741143047930, 362498797935140573⟩, ⟨(-834919859664051461), (-832535754121772657)⟩, true⟩

def words04 : List Nat := [371285401620222004, 371285401622545511, 371285401641414901, 371285401782073135, 371285401877663898, 371285401879812603, 371285401921177244, 371285402040038468, 371285402345585042, 371285402563318370]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk621A
