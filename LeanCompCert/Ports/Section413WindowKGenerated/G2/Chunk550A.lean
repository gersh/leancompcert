import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk550A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360540972903951975, 360540992028697120⟩, ⟨2241792271836542638, 2242502958391420826⟩, true⟩

def state01 : KState := ⟨⟨360596297240813343, 360596316372767809⟩, ⟨(-801329125093824337), (-800618041989660607)⟩, true⟩

def words00 : List Nat := [360581764069067090, 360581763658491860, 360581763442874765, 360581763326135889, 360581763209343250, 360581762822341886, 360581762443523912, 360581762294952259, 360581762326493849, 360581762591851453]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565471427843530, 360565490567091614⟩, ⟨894526865666851241, 895238350029068489⟩, true⟩

def words01 : List Nat := [360581762607906153, 360581762624041232, 360581762624670874, 360581762621569677, 360581762632869754, 360581762644298938, 360581762644986685, 360581762490229987, 360581762006071041, 360581761711221550]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570754830873881, 360570773977324627⟩, ⟨603900441356880571, 604612322045369005⟩, true⟩

def words02 : List Nat := [360581761450014567, 360581761582191439, 360581761582872893, 360581761550160059, 360581761517323305, 360581761322070209, 360581761294477378, 360581761256637504, 360581761218720721, 360581760935748130]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603138221132189, 360603157374796299⟩, ⟨(-1178340802884984527), (-1177628525207640893)⟩, true⟩

def words03 : List Nat := [360581760805422982, 360581760874970069, 360581760994583240, 360581761122520083, 360581761123232143, 360581760969462905, 360581760883275130, 360581761117544021, 360581761506903626, 360581761896421858]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609038803879177, 360609057964844114⟩, ⟨(-1503293068851068082), (-1502580389301388270)⟩, true⟩

def words04 : List Nat := [360581762030026733, 360581762214548140, 360581762545209057, 360581762876094695, 360581763073099153, 360581763158826916, 360581763159508872, 360581763041569527, 360581763134010292, 360581763630693938]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk550A
