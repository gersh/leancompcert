import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk510A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566332720851340, 360566349064335798⟩, ⟨795181124205172719, 795744328670476743⟩, true⟩

def state01 : KState := ⟨⟨360571643256776731, 360571659606902275⟩, ⟨524398916701693600, 524962459897020500⟩, true⟩

def words00 : List Nat := [360581951666605598, 360581951755295991, 360581951755930373, 360581951651883820, 360581951547726097, 360581951303596247, 360581951260872341, 360581951269018914, 360581951269657932, 360581950970554442]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609234721215331, 360609251077997900⟩, ⟨(-1393383896982249657), (-1392820014179016205)⟩, true⟩

def words01 : List Nat := [360581950776744231, 360581950784898758, 360581951095261036, 360581951227801248, 360581951228452725, 360581951046307594, 360581950864023951, 360581951050939145, 360581951586594129, 360581952122387877]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360567947471785933, 360567963835299101⟩, ⟨713135591412933945, 713699817643040527⟩, true⟩

def words02 : List Nat := [360581952464649073, 360581952547505038, 360581952548085417, 360581952516930266, 360581952485593103, 360581952228533231, 360581951748904254, 360581951053926739, 360581950358845243, 360581949722378134]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360550713642329862, 360550730012483783⟩, ⟨1592796997229416217, 1593361562370487909⟩, true⟩

def words03 : List Nat := [360581949557896762, 360581949667612693, 360581949668241028, 360581949585803984, 360581949582159569, 360581949400480038, 360581949218611566, 360581948908559168, 360581948522345238, 360581947911433049]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595232737737416, 360595249114541315⟩, ⟨(-679659335470164597), (-679094430880676135)⟩, true⟩

def words04 : List Nat := [360581947300379722, 360581946932743738, 360581947016336760, 360581947250011794, 360581947250662696, 360581947138397656, 360581946643263044, 360581946531212255, 360581946578435318, 360581946839740025]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk510A
