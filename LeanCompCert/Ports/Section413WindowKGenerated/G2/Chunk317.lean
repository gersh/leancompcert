import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk317

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360613231197909429, 360613237270324437⟩, ⟨(-975762784910321996), (-975632615278439270)⟩, true⟩

def state01 : KState := ⟨⟨360581333059507295, 360581339135943892⟩, ⟨35335798911679155, 35466096047786949⟩, true⟩

def words00 : List Nat := [360582461661763454, 360582462079483104, 360582462454199697, 360582462829010027, 360582462829364061, 360582462600615878, 360582461685712263, 360582460133773316, 360582458581851842, 360582457587411814]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360481852291853349, 360481858372261563⟩, ⟨3190547800600093406, 3190678223696359308⟩, true⟩

def words01 : List Nat := [360582457955321290, 360582458358555459, 360582458358934151, 360582458011826043, 360582457020266885, 360582455779834343, 360582454539358743, 360582452960827227, 360582450389972585, 360582447219162458]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602554174212853, 360602560258603975⟩, ⟨(-638716307799788616), (-638585758346457754)⟩, true⟩

def words02 : List Nat := [360582444048454833, 360582441867938779, 360582440387049016, 360582439896148255, 360582439405239853, 360582438054517057, 360582436212048195, 360582435359436851, 360582434643342826, 360582435278037764]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580050014334436, 360580056102751578⟩, ⟨75390729894383895, 75521407113091657⟩, true⟩

def words03 : List Nat := [360582435278420339, 360582435143560770, 360582435167959379, 360582436021384963, 360582436206160721, 360582436390991407, 360582436391367703, 360582435954670825, 360582435553642176, 360582435479157158]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594648547750934, 360594654640144353⟩, ⟨(-388045464322336082), (-387914660876942362)⟩, true⟩

def words04 : List Nat := [360582436318466852, 360582436633355548, 360582436633735317, 360582436445485066, 360582436257183600, 360582435414009522, 360582436103452689, 360582436792933174, 360582436855112041, 360582437240349798]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360602902732253187, 360602908828641584⟩, ⟨(-650026514050875048), (-649895583745516070)⟩, true⟩

def words05 : List Nat := [360582438613823563, 360582439987347341, 360582442143928939, 360582443310445982, 360582443619152474, 360582443927873396, 360582444390161776, 360582445476245834, 360582446120907356, 360582446765616317]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605997472515465, 360606003572930315⟩, ⟨(-748692143779259055), (-748561085573242803)⟩, true⟩

def words06 : List Nat := [360582446908261247, 360582446908684034, 360582446061555490, 360582445665401709, 360582445269161131, 360582444624481820, 360582444014704545, 360582442910049366, 360582441805379227, 360582442429574008]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360523128299140685, 360523134403544187⟩, ⟨1884665031447896604, 1884796216392929376⟩, true⟩

def words07 : List Nat := [360582444158458590, 360582445887317319, 360582446715427917, 360582446715850894, 360582446554884871, 360582445828737386, 360582445102512064, 360582444991213885, 360582443891012171, 360582442025205387]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575489666269307, 360575495774666031⟩, ⟨220334581596113521, 220465893465144881⟩, true⟩

def words08 : List Nat := [360582440159413078, 360582438966103292, 360582438273983019, 360582438138830252, 360582438003654444, 360582437003259659, 360582435560792559, 360582433744797649, 360582431928789035, 360582430845237442]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614204500669302, 360614210613091895⟩, ⟨(-1010646940515274292), (-1010515500643431208)⟩, true⟩

def words09 : List Nat := [360582430627468818, 360582429916074772, 360582429478273856, 360582430514645277, 360582431303646537, 360582432092667184, 360582432381204493, 360582432395950112, 360582433395607519, 360582434395342660]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk317
