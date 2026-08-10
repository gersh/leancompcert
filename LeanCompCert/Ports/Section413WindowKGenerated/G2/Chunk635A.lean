import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk635A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360611147588713198, 360611173375797316⟩, ⟨(-1809049333130720349), (-1807943175950060173)⟩, true⟩

def state01 : KState := ⟨⟨360575689481142244, 360575715276724215⟩, ⟨442546503771351568, 443653200606217768⟩, true⟩

def words00 : List Nat := [360582702575116992, 360582702625145813, 360582702625873301, 360582702612752631, 360582702599371880, 360582702449982613, 360582702104677402, 360582701634727802, 360582701164622444, 360582700841211796]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562413523938354, 360562439327938173⟩, ⟨1285732981147780854, 1286840212642160000⟩, true⟩

def words01 : List Nat := [360582700731956525, 360582700555708895, 360582700379374437, 360582700079980190, 360582699742026527, 360582699341786226, 360582698941298012, 360582698648258949, 360582698465423749, 360582698147406721]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592851234497593, 360592877046919135⟩, ⟨(-647746975539234206), (-646639209055407644)⟩, true⟩

def words02 : List Nat := [360582697829197492, 360582697813045013, 360582698066597787, 360582698320313554, 360582698321157742, 360582698317183992, 360582698330325265, 360582698461293367, 360582698560097675, 360582698721234739]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570545025900598, 360570570846843584⟩, ⟨769560746328292017, 770669054221494295⟩, true⟩

def words03 : List Nat := [360582698726471578, 360582698731809246, 360582698984482201, 360582699361152614, 360582699623878009, 360582699886748716, 360582700024843437, 360582700025736432, 360582699917003877, 360582699727142947]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360565812713041941, 360565838542396481⟩, ⟨1070256755110883791, 1071365597514307873⟩, true⟩

def words04 : List Nat := [360582699593580021, 360582699594473080, 360582699405117689, 360582699063534344, 360582698721811671, 360582698278595475, 360582698060269778, 360582697816552208, 360582697572753403, 360582697167062324]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk635A
