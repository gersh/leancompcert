import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk212A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360671270303782811, 360671272925943260⟩, ⟨(-1921405305835476961), (-1921367690444045347)⟩, true⟩

def state01 : KState := ⟨⟨360595554736527785, 360595557361292799⟩, ⟨(-316463632792789932), (-316425962171971274)⟩, true⟩

def words00 : List Nat := [360580649445328494, 360580650026304990, 360580650026530805, 360580649597671240, 360580649168776642, 360580648182851182, 360580646231659243, 360580643174608494, 360580640117792176, 360580639348838320]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360483033972571109, 360483036599907290⟩, ⟨2071020944283450271, 2071058669452063287⟩, true⟩

def words01 : List Nat := [360580642263657579, 360580645178254208, 360580646967282457, 360580646967555752, 360580646544325495, 360580645565793710, 360580644587276175, 360580643475734505, 360580640571039386, 360580635971700507]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360556871689867560, 360556874319783944⟩, ⟨503962743417611354, 504000523350788008⟩, true⟩

def words02 : List Nat := [360580631372733553, 360580628983694197, 360580627800130146, 360580627581306926, 360580627362478498, 360580625309248074, 360580621046167922, 360580618991742708, 360580616937432466, 360580614335014787]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567928189752656, 360567930822276041⟩, ⟨268935252080721092, 268973087373519970⟩, true⟩

def words03 : List Nat := [360580613217087759, 360580610353622450, 360580607490375275, 360580605353298515, 360580604337118932, 360580602267346424, 360580600197738958, 360580597025250676, 360580594934555165, 360580594338630727]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598111050696280, 360598113685795846⟩, ⟨(-372451770475822857), (-372413880452041581)⟩, true⟩

def words04 : List Nat := [360580593742670893, 360580593777836226, 360580593778080009, 360580592692788625, 360580591607558629, 360580588959886825, 360580588106499473, 360580588782043453, 360580588782289704, 360580589151399722]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk212A
