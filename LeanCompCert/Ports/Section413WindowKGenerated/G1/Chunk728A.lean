import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk728A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493397949972387, 362493476844485403⟩, ⟨(-600286829436207877), (-596408032813022803)⟩, true⟩

def state01 : KState := ⟨⟨362476633865609018, 362476712782655574⟩, ⟨620205498712493239, 624085935895961487⟩, true⟩

def words00 : List Nat := [371285284652297793, 371285284654798160, 371285284582675322, 371285284628176808, 371285284729879162, 371285284732379974, 371285284607469968, 371285284444204166, 371285284279908744, 371285284214270682]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476474128513348, 362476553068055974⟩, ⟨631877899557736449, 635759974792945067⟩, true⟩

def words01 : List Nat := [371285284100711474, 371285284105864331, 371285284107742397, 371285284110211926, 371285283957671619, 371285283863829570, 371285283860155811, 371285283862660040, 371285283753324616, 371285283636234949]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485420657560566, 362485499619507707⟩, ⟨(-19641368323869143), (-15757661477709221)⟩, true⟩

def words02 : List Nat := [371285283518070177, 371285283451580339, 371285283333653223, 371285283370750929, 371285283375873704, 371285283378386573, 371285283203000113, 371285283167967600, 371285283254685155, 371285283260244788]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481648121815033, 362481727106542172⟩, ⟨255151487880885644, 259036853910058608⟩, true⟩

def words03 : List Nat := [371285283262127056, 371285283229525500, 371285283331499122, 371285283384451835, 371285283443863981, 371285283504179580, 371285283562677819, 371285283565179530, 371285283396806408, 371285283351104364]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483022679269976, 362483101686319386⟩, ⟨155063042326061971, 158950034422006943⟩, true⟩

def words04 : List Nat := [371285283388895232, 371285283391458723, 371285283382790016, 371285283375578760, 371285283372604809, 371285283375396144, 371285283409253227, 371285283506943296, 371285283564773016, 371285283567368419]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk728A
