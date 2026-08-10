import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk686A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589924072154272, 360589954353844454⟩, ⟨(-489286889585528254), (-487883705618735222)⟩, true⟩

def state01 : KState := ⟨⟨360554621410308776, 360554651701231353⟩, ⟨1932572671264734164, 1933976488620129266⟩, true⟩

def words00 : List Nat := [360582842451014294, 360582842422759920, 360582842182113684, 360582842069579128, 360582841956790911, 360582841790743683, 360582841412430458, 360582840836341829, 360582840260086929, 360582839669291696]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566329209588512, 360566359509646926⟩, ⟨1129313818260059168, 1130718262470929380⟩, true⟩

def words01 : List Nat := [360582839259238610, 360582839061419961, 360582838863498629, 360582838559556214, 360582838382993072, 360582838153322118, 360582837923363483, 360582837836333851, 360582837718211914, 360582837479079613]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360560329339326948, 360560359648557663⟩, ⟨1541104818390302445, 1542509892048708123⟩, true⟩

def words02 : List Nat := [360582837239747645, 360582836996176125, 360582836886842415, 360582836915448183, 360582836916352625, 360582836756857670, 360582836385114294, 360582836076050780, 360582835766697837, 360582835386457251]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556269263748260, 360556299582218913⟩, ⟨1819779335119536263, 1821185042959385353⟩, true⟩

def words03 : List Nat := [360582835059835140, 360582834627248003, 360582834194486261, 360582833973910442, 360582833891765280, 360582833629361823, 360582833366860224, 360582832981405109, 360582832383776477, 360582831998345944]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564434430849824, 360564464758465346⟩, ⟨1259309788050834756, 1260716123640716788⟩, true⟩

def words04 : List Nat := [360582831612591911, 360582831389685436, 360582831173378488, 360582830823112432, 360582830472698317, 360582830069283921, 360582829811511818, 360582829647132723, 360582829482667838, 360582829159392378]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk686A
