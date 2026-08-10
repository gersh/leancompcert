import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk553A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582056240125709, 360582075582593680⟩, ⟨(-14640884588100966), (-13918190593531384)⟩, true⟩

def state01 : KState := ⟨⟨360579020531886822, 360579039881613770⟩, ⟨153326640838307578, 154049736290580602⟩, true⟩

def words00 : List Nat := [360581824016049143, 360581824337884603, 360581824836195675, 360581825334636158, 360581825553839309, 360581825554608637, 360581825448039994, 360581825333951951, 360581825219638397, 360581825087476916]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567518032716657, 360567537389770285⟩, ⟨789642467253556494, 790365967980940888⟩, true⟩

def words01 : List Nat := [360581825037807009, 360581824802540279, 360581824657150000, 360581825002206108, 360581825063679739, 360581825125272452, 360581825125958003, 360581825024599962, 360581824812164643, 360581824554773556]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360563637888820967, 360563657253131023⟩, ⟨1004191112205013628, 1004915014394939196⟩, true⟩

def words02 : List Nat := [360581824297147451, 360581824029702079, 360581823507517579, 360581822822903420, 360581822138189214, 360581821368411573, 360581820762026874, 360581820382967783, 360581820003819693, 360581819461957970]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360616744543590754, 360616763915158145⟩, ⟨(-1934513509492101834), (-1933789205718341118)⟩, true⟩

def words03 : List Nat := [360581819134333729, 360581819132762711, 360581819454324561, 360581819547074422, 360581819547799016, 360581819319619674, 360581819188134075, 360581819494690297, 360581820126762379, 360581820758986079]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607988450518887, 360608007829435316⟩, ⟨(-1449956134073894763), (-1449231423570230287)⟩, true⟩

def words04 : List Nat := [360581821108070875, 360581821573425788, 360581822364321441, 360581823155414407, 360581823864078668, 360581824247660467, 360581824429599529, 360581824611614741, 360581824785663901, 360581825259588878]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk553A
