import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk413A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595527347769849, 360595537881580388⟩, ⟨(-544470163717759463), (-544176142248547885)⟩, true⟩

def state01 : KState := ⟨⟨360576481283441835, 360576491822601156⟩, ⟨242007933628781672, 242302176028013742⟩, true⟩

def words00 : List Nat := [360582362023337104, 360582361963287608, 360582361473646865, 360582361422415853, 360582361371042129, 360582360935703750, 360582360250299988, 360582359119698133, 360582357989043016, 360582357283168283]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575032468586503, 360575043013029168⟩, ⟨301990600166108096, 302285060846787724⟩, true⟩

def words01 : List Nat := [360582357459361592, 360582357777629794, 360582357778130171, 360582358022209338, 360582358131794312, 360582358241526532, 360582358778924419, 360582358897149732, 360582358897654653, 360582358721181317]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360559990821825184, 360560001371576950⟩, ⟨923614840730655150, 923909520808827856⟩, true⟩

def words02 : List Nat := [360582358544597499, 360582358556568496, 360582358945420301, 360582359334360115, 360582359334880032, 360582359241011562, 360582358564526971, 360582357537983494, 360582356511308930, 360582355824052364]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565241997762767, 360565252552858244⟩, ⟨706522851979219365, 706817752939835575⟩, true⟩

def words03 : List Nat := [360582355283689369, 360582354359258999, 360582353434766045, 360582353094396635, 360582353063292966, 360582352627094160, 360582352190860437, 360582351457538547, 360582350637629152, 360582350224675851]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587022254946011, 360587032815337232⟩, ⟨(-193901686214379509), (-193606566300706495)⟩, true⟩

def words04 : List Nat := [360582349981706333, 360582350166703900, 360582350167204381, 360582350059494375, 360582349951695468, 360582349733486239, 360582350226327646, 360582350719252592, 360582350719765219, 360582350786697037]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk413A
