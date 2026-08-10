import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk873A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578204780769991, 360578254758883742⟩, ⟨338269268321735217, 341215685195686869⟩, true⟩

def state01 : KState := ⟨⟨360567957572756478, 360568007562699562⟩, ⟨1232889116240558288, 1235836565875788942⟩, true⟩

def words00 : List Nat := [360582163306174585, 360582163307431348, 360582163226844493, 360582163080727687, 360582162934389521, 360582162726055078, 360582162583379614, 360582162461378740, 360582162339246192, 360582162144830771]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588868097813788, 360588918099638029⟩, ⟨(-592981471447135206), (-590032984413507476)⟩, true⟩

def words01 : List Nat := [360582161983747617, 360582161819689048, 360582161655261164, 360582161622084951, 360582161487291707, 360582161241112928, 360582160994698697, 360582160885435855, 360582160963837231, 360582161042522175]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566931571776694, 360566981585565795⟩, ⟨1322564394451089512, 1325513926314661680⟩, true⟩

def words02 : List Nat := [360582161043647357, 360582161038981260, 360582160903033009, 360582160898444098, 360582160893538537, 360582160798403106, 360582160615976016, 360582160359201377, 360582160102201377, 360582159805264807]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360550754465657273, 360550804491300995⟩, ⟨2735442479936924679, 2738393047125710323⟩, true⟩

def words03 : List Nat := [360582159632481349, 360582159521880202, 360582159411122915, 360582159224446557, 360582158999849879, 360582158742642241, 360582158485058147, 360582158358665398, 360582158101173662, 360582157743500740]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582014278073065, 360582064315577334⟩, ⟨5053756814612471, 8005359962623565⟩, true⟩

def words04 : List Nat := [360582157385541846, 360582157134645636, 360582156949309819, 360582156821957624, 360582156694522167, 360582156456908583, 360582156276873011, 360582156136341991, 360582155995443599, 360582155962514514]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk873A
