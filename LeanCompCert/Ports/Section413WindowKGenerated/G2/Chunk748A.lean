import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk748A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360547992077682452, 360548028328524632⟩, ⟨2561170941756755004, 2563002400405023102⟩, true⟩

def state01 : KState := ⟨⟨360562493105365820, 360562529366266459⟩, ⟨1476469729958672637, 1478301941029668839⟩, true⟩

def words00 : List Nat := [360582292609280209, 360582292292461228, 360582292123775568, 360582291962992280, 360582291802130658, 360582291489055084, 360582291038355584, 360582290733532198, 360582290428408683, 360582290119388097]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546677456452027, 360546713727492049⟩, ⟨2659739976027259841, 2661572945674574471⟩, true⟩

def words01 : List Nat := [360582289856200985, 360582289457051844, 360582289057709442, 360582288792064543, 360582288644303477, 360582288398576993, 360582288152734891, 360582287773825649, 360582287216240622, 360582286742002536]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568460501336194, 360568496782422169⟩, ⟨1029814269866806985, 1031647991202966313⟩, true⟩

def words02 : List Nat := [360582286267422064, 360582285971447187, 360582285722402896, 360582285336013670, 360582284949462361, 360582284467069187, 360582284073347094, 360582283858200156, 360582283642937884, 360582283338498649]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590014764516337, 360590051055643748⟩, ⟨(-583199011729892466), (-581364538941840178)⟩, true⟩

def words03 : List Nat := [360582283155123901, 360582283150404326, 360582283167179117, 360582283208142580, 360582283209134123, 360582283099362063, 360582282989403789, 360582282875669319, 360582282955410478, 360582283060307745]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579066947691193, 360579103248967600⟩, ⟨236109394257465735, 237944626643664717⟩, true⟩

def words04 : List Nat := [360582283061263484, 360582283033518851, 360582282987632523, 360582283054607701, 360582283076336232, 360582283077401522, 360582282920820392, 360582282658300732, 360582282395584977, 360582282201895372]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk748A
