import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk413

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

def state06 : KState := ⟨⟨360655469909115796, 360655480474808805⟩, ⟨(-3024595072445910707), (-3024299733277207851)⟩, true⟩

def words05 : List Nat := [360582351483741007, 360582352180915690, 360582353047205955, 360582354005143786, 360582354461398546, 360582354917679983, 360582355957020718, 360582357338942441, 360582359107364497, 360582360875832059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360628571520246756, 360628582091297880⟩, ⟨(-1912249231613141509), (-1911953670806553307)⟩, true⟩

def words06 : List Nat := [360582362230343070, 360582363003341986, 360582363564600686, 360582364125994211, 360582364538345082, 360582365074539553, 360582365318453856, 360582365562417584, 360582366145013849, 360582367262775327]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564028457717117, 360564039034058547⟩, ⟨758294936491213612, 758590716185041700⟩, true⟩

def words07 : List Nat := [360582368469835952, 360582369676942693, 360582370589785718, 360582371090928109, 360582371415086348, 360582371739377040, 360582371853589305, 360582371854153030, 360582371779946705, 360582371337494629]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360630145530232166, 360630156111879011⟩, ⟨(-1977930822888377771), (-1977634823630256759)⟩, true⟩

def words08 : List Nat := [360582371034456939, 360582371647853301, 360582372565300899, 360582373482820985, 360582373907665745, 360582373908228146, 360582374178029607, 360582374604468835, 360582375613021269, 360582376767972601]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617022779766898, 360617033366783864⟩, ⟨(-1434861284728053916), (-1434565063174666458)⟩, true⟩

def words09 : List Nat := [360582377466374194, 360582378164792019, 360582378753607951, 360582379633954688, 360582380167600081, 360582380701310153, 360582380943120665, 360582381198642771, 360582382036106665, 360582382873723922]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk413
