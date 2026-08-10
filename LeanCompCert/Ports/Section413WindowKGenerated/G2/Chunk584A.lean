import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk584A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602823333721123, 360602845000377666⟩, ⟨(-1219158065763077887), (-1218303206619864069)⟩, true⟩

def state01 : KState := ⟨⟨360600522057520791, 360600543731962958⟩, ⟨(-1084917798562501576), (-1084062484702773348)⟩, true⟩

def words00 : List Nat := [360581984125860099, 360581984126675631, 360581984083315197, 360581984208845733, 360581984259034803, 360581984332385269, 360581984333111762, 360581984258812295, 360581984195241368, 360581984513926925]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571888685201035, 360571910367309836⟩, ⟨587785567873878708, 588641329581778040⟩, true⟩

def words01 : List Nat := [360581985125505438, 360581985737221507, 360581986201226006, 360581986372930129, 360581986373624536, 360581986347628079, 360581986587639094, 360581986588454817, 360581986563071270, 360581986391438248]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580407206289089, 360580428896112411⟩, ⟨90128486427387896, 90984698854026436⟩, true⟩

def words02 : List Nat := [360581986219629767, 360581986042850264, 360581986241281879, 360581986439862879, 360581986440617810, 360581986378709691, 360581986129865018, 360581986152548908, 360581986153221749, 360581986053375017]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574203561788240, 360574225259376393⟩, ⟨452624298992986850, 453480965157585526⟩, true⟩

def words03 : List Nat := [360581986027452262, 360581985854098157, 360581985712604953, 360581985891691167, 360581985892378325, 360581985851261944, 360581985810050706, 360581985586399013, 360581985161338690, 360581985029485182]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583235070282097, 360583256775569546⟩, ⟨(-75303894172005416), (-74446778022925904)⟩, true⟩

def words04 : List Nat := [360581985057501660, 360581985058317759, 360581984927143875, 360581984519618079, 360581984111971300, 360581983629555590, 360581983353800434, 360581983315825876, 360581983277759596, 360581983114245995]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk584A
