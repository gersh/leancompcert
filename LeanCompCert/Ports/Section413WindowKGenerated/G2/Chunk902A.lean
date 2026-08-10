import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk902A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360606897928597604, 360606951417280685⟩, ⟨(-2255479292354204155), (-2252221282675307103)⟩, true⟩

def state01 : KState := ⟨⟨360616548267745892, 360616601768834562⟩, ⟨(-3126008751469686850), (-3122749622747770152)⟩, true⟩

def words00 : List Nat := [360581982712408472, 360581982978647963, 360581983367419761, 360581983756565540, 360581984114420860, 360581984477820405, 360581984762052630, 360581985046403059, 360581985321025579, 360581985706239671]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593117710073257, 360593171223424912⟩, ⟨(-1012206833450572809), (-1008946598424597839)⟩, true⟩

def words01 : List Nat := [360581986073056196, 360581986440109731, 360581986745303409, 360581986972909430, 360581987169381095, 360581987366232680, 360581987685433131, 360581987915854849, 360581988040975136, 360581988166282733]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615749123213196, 360615802648864421⟩, ⟨(-3054140318391811659), (-3050878973637820881)⟩, true⟩

def words02 : List Nat := [360581988386831268, 360581988701840120, 360581989013505354, 360581989325395058, 360581989533089202, 360581989643688347, 360581989876778457, 360581990110246423, 360581990401303804, 360581990777405191]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360600149965591965, 360600203503640490⟩, ⟨(-1646573538880982073), (-1643311075455455011)⟩, true⟩

def words03 : List Nat := [360581991079233243, 360581991381194321, 360581991643551800, 360581991971551874, 360581992268295030, 360581992565247838, 360581992768159349, 360581992848551546, 360581993051406629, 360581993254690950]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596811071114997, 360596864621428242⟩, ⟨(-1345328239095028812), (-1342064668842001670)⟩, true⟩

def words04 : List Nat := [360581993468545608, 360581993560012568, 360581993570323254, 360581993580796050, 360581993581885864, 360581993621102598, 360581993804359973, 360581993987864245, 360581994097428839, 360581994263550302]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk902A
