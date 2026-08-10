import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk424A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360536440408152996, 360536451534468953⟩, ⟨1953889437139247222, 1954208256462816460⟩, true⟩

def state01 : KState := ⟨⟨360634629266854650, 360634640398620101⟩, ⟨(-2209822015375199518), (-2209502964966102662)⟩, true⟩

def words00 : List Nat := [360582540265306928, 360582539620015261, 360582539623798075, 360582539903900137, 360582539904436104, 360582539630515162, 360582540142558020, 360582540676791735, 360582541766450422, 360582542995470775]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589045321648124, 360589056458921529⟩, ⟨(-276383882152043432), (-276064598123833680)⟩, true⟩

def words01 : List Nat := [360582543883030886, 360582544770612968, 360582545526722123, 360582546559481800, 360582547263093399, 360582547966768613, 360582548389695653, 360582548416618561, 360582548570507126, 360582548724588915]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360547789941594368, 360547801084302714⟩, ⟨1473887114021134436, 1474206628627773928⟩, true⟩

def words02 : List Nat := [360582549244810675, 360582549245388437, 360582549212791057, 360582548869150325, 360582548525432168, 360582548041380166, 360582547838511770, 360582547160462347, 360582546482381850, 360582545525231957]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360615713779821978, 360615724927985712⟩, ⟨(-1408465507793574729), (-1408145761687924269)⟩, true⟩

def words03 : List Nat := [360582544706853662, 360582544321840925, 360582544106070555, 360582544309340688, 360582544309879479, 360582543964577676, 360582543828271645, 360582544461741559, 360582545244030139, 360582546026412047]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572123989766161, 360572135143443750⟩, ⟨441571982397543342, 441891962538244172⟩, true⟩

def words04 : List Nat := [360582546344173286, 360582546344751382, 360582546429732484, 360582546750018159, 360582546770470301, 360582546771049679, 360582546550380896, 360582546050891334, 360582545551309187, 360582544848097184]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk424A
