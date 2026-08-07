import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk501

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472644831942755, 362472681106485809⟩, ⟨615766413055224617, 616994211837515153⟩, true⟩

def state01 : KState := ⟨⟨362475832266362863, 362475868555789943⟩, ⟨456132226355483729, 457360770906591999⟩, true⟩

def words00 : List Nat := [371284996267590395, 371284996269271736, 371284996135947612, 371284995999457965, 371284995862327957, 371284995739610543, 371284995542992509, 371284995616282185, 371284995689778255, 371284995691509492]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499896130744199, 362499932435341885⟩, ⟨(-749837479665824287), (-748608174843569209)⟩, true⟩

def words01 : List Nat := [371284995726057045, 371284995943646574, 371284996326062602, 371284996327735215, 371284996179985824, 371284995998288305, 371284995915598728, 371284995917441786, 371284996117077713, 371284996417009379]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490648743141490, 362490685062836925⟩, ⟨(-286354499140388751), (-285124437541324245)⟩, true⟩

def words02 : List Nat := [371284996714677580, 371284996716354126, 371284996888145217, 371284997174192857, 371284997574329547, 371284997576002850, 371284997500410646, 371284997322038037, 371284997360182297, 371284997475564752]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498975120645748, 362499011455378849⟩, ⟨(-703734892089565906), (-702504076574818212)⟩, true⟩

def words03 : List Nat := [371284997987560126, 371284998500199700, 371284998958038944, 371284999085732580, 371284999281517214, 371284999478133824, 371285000040445154, 371285000321659559, 371285000602364241, 371285000883659601]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492626944155149, 362492663293900199⟩, ⟨(-385390929905813542), (-384159361616629004)⟩, true⟩

def words04 : List Nat := [371285001182166076, 371285001299847660, 371285001718179298, 371285002137196983, 371285002488260929, 371285002489934829, 371285002528449557, 371285002747741985, 371285003085547924, 371285003240030553]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502521631971996, 362502557996977600⟩, ⟨(-881641826876740529), (-880409493195094093)⟩, true⟩

def words05 : List Nat := [371285003381830597, 371285003524203696, 371285004062965681, 371285004454293151, 371285004858368863, 371285005263032866, 371285005665832783, 371285005667508349, 371285005971474063, 371285006323502289]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491051550704482, 362491087930631708⟩, ⟨(-306171200861833872), (-304938118632775408)⟩, true⟩

def words06 : List Nat := [371285007026002843, 371285007398863422, 371285007739478826, 371285008080628003, 371285008518082344, 371285008760158784, 371285009143037921, 371285009526588047, 371285009832053294, 371285009954935933]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362512164655398324, 362512201050447357⟩, ⟨(-1365537698118852540), (-1364303857153071206)⟩, true⟩

def words07 : List Nat := [371285010281301841, 371285010608496371, 371285011290377079, 371285011443661584, 371285011510263138, 371285011577425231, 371285012040596446, 371285012305985176, 371285012848948874, 371285013392625611]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496220304461672, 362496256714642833⟩, ⟨(-565440937093099940), (-564206336721348074)⟩, true⟩

def words08 : List Nat := [371285013919592935, 371285014091515521, 371285014373034702, 371285014655429107, 371285015058673016, 371285015060350720, 371285015037241190, 371285015015074359, 371285015303320211, 371285015529236658]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472150010931610, 362472186436201760⟩, ⟨642859243578361510, 644094601343580354⟩, true⟩

def words09 : List Nat := [371285016090390106, 371285016652223208, 371285017145637940, 371285017147313683, 371285017197129496, 371285017284312466, 371285017475326592, 371285017477006135, 371285017259644323, 371285017005949641]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk501
