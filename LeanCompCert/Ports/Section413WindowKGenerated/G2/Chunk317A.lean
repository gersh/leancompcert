import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk317A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk317A
