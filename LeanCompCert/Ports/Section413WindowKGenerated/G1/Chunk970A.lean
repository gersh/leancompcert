import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk970A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476912417707795, 362477055619308602⟩, ⟨792933705272846634, 802311972733328328⟩, true⟩

def state01 : KState := ⟨⟨362495469602369258, 362495612834439861⟩, ⟨(-1007167572943592138), (-997786349760805288)⟩, true⟩

def words00 : List Nat := [371285326814943600, 371285326818740150, 371285326883999560, 371285326972343220, 371285327034187582, 371285327041218103, 371285327153479246, 371285327267553678, 371285327434051689, 371285327543599021]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491502312261495, 362491645575393342⟩, ⟨(-622258872374019009), (-612874635794400663)⟩, true⟩

def words01 : List Nat := [371285327651740758, 371285327760974072, 371285327912861655, 371285328032476746, 371285328182641960, 371285328334140249, 371285328487436110, 371285328510892314, 371285328578328738, 371285328647761238]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485400952395138, 362485544245781824⟩, ⟨(-30249348407442940), (-20862176344618516)⟩, true⟩

def words02 : List Nat := [371285328821552462, 371285328864330806, 371285328905871728, 371285328948611781, 371285329022730066, 371285329048589609, 371285329110032856, 371285329172790316, 371285329234768416, 371285329240511915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502468319135446, 362502611643346254⟩, ⟨(-1686395733652928806), (-1677005570572090004)⟩, true⟩

def words03 : List Nat := [371285329299274578, 371285329359837292, 371285329496567434, 371285329564141089, 371285329614695877, 371285329666290038, 371285329792731826, 371285329868283190, 371285330048680899, 371285330230638511]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494146679294724, 362494290034237913⟩, ⟨(-878850913609147946), (-869457768097660634)⟩, true⟩

def words04 : List Nat := [371285330390719105, 371285330458518465, 371285330616178198, 371285330775564235, 371285330953878986, 371285330991607838, 371285331017690360, 371285331044993765, 371285331166174051, 371285331262374690]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk970A
