import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk706A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360553444942446592, 360553477088972266⟩, ⟨2043583313584028689, 2045116299607303313⟩, true⟩

def state01 : KState := ⟨⟨360567978407748849, 360568010563734004⟩, ⟨1017484511701960650, 1019018165610578336⟩, true⟩

def words00 : List Nat := [360582444332451449, 360582443991852926, 360582443823855250, 360582443715297243, 360582443606672037, 360582443327211345, 360582442924288294, 360582442721841092, 360582442519126023, 360582442204657536]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582054158630008, 360582086324144601⟩, ⟨23479721873189817, 25014048701529769⟩, true⟩

def words01 : List Nat := [360582442001166767, 360582441697462962, 360582441393576175, 360582441257657871, 360582441221484439, 360582441094006874, 360582440966401658, 360582440738619708, 360582440534308349, 360582440530441706]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589282821636739, 360589314996581019⟩, ⟨(-487105620484623074), (-485570627684846838)⟩, true⟩

def words02 : List Nat := [360582440721313019, 360582440722313712, 360582440718105247, 360582440542610598, 360582440366958852, 360582440133233486, 360582440102104623, 360582440187168084, 360582440188064089, 360582440244309569]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586213616155649, 360586245800539703⟩, ⟨(-270398961132207671), (-268863301554340517)⟩, true⟩

def words03 : List Nat := [360582440373903796, 360582440503794103, 360582440635893699, 360582440636894567, 360582440568946738, 360582440309211405, 360582440049305936, 360582439785306583, 360582439693875650, 360582439748791366]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581199931799449, 360581232125728830⟩, ⟨83759394070736645, 85295727975155177⟩, true⟩

def words04 : List Nat := [360582439749692036, 360582439729147897, 360582439895056549, 360582440061274100, 360582440150192185, 360582440151193273, 360582440040052720, 360582439828820432, 360582439617403636, 360582439425487856]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk706A
