import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk812A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493909142624189, 362494008125172946⟩, ⟨(-722000649533929861), (-716573429711423317)⟩, true⟩

def state01 : KState := ⟨⟨362487330362834273, 362487429370691419⟩, ⟨(-187778449047208021), (-182349174050388171)⟩, true⟩

def words00 : List Nat := [371285183548737328, 371285183551566530, 371285183650952328, 371285183778832455, 371285183941133626, 371285183946743428, 371285183948900891, 371285183924420561, 371285183964529332, 371285183995384498]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479083256081320, 362479182289225576⟩, ⟨482051401526590104, 487482730214889402⟩, true⟩

def words01 : List Nat := [371285184125318594, 371285184256359463, 371285184347746629, 371285184350606369, 371285184316051226, 371285184311079128, 371285184432624071, 371285184435434909, 371285184363563663, 371285184292798771]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486022916909504, 362486121975249796⟩, ⟨(-81612352138931950), (-76178976900802448)⟩, true⟩

def words02 : List Nat := [371285184220842071, 371285184186558516, 371285184113631014, 371285184155100037, 371285184180079473, 371285184182898280, 371285184052657101, 371285184049908288, 371285184154083866, 371285184168539294]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487636510774609, 362487735594729519⟩, ⟨(-212679793339805567), (-207244337293947617)⟩, true⟩

def words03 : List Nat := [371285184182257466, 371285184196962141, 371285184361992894, 371285184452814116, 371285184522848649, 371285184593889581, 371285184661687123, 371285184664498837, 371285184577713426, 371285184612623268]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489271108510884, 362489370217556473⟩, ⟨(-345458931594972953), (-340021437053249663)⟩, true⟩

def words04 : List Nat := [371285184778892974, 371285184820602548, 371285184834198339, 371285184848696603, 371285184908703593, 371285184916201246, 371285185063872895, 371285185212725468, 371285185335402664, 371285185389836775]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk812A
