import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk478A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360531086400665277, 360531100681757539⟩, ⟨2464444086947284027, 2464905370879100743⟩, true⟩

def state01 : KState := ⟨⟨360592506059288054, 360592520346596426⟩, ⟨(-471864739944974594), (-471403158852445452)⟩, true⟩

def words00 : List Nat := [360582666661473639, 360582665712971412, 360582665016390595, 360582664309524542, 360582663602633244, 360582662520298108, 360582661558480152, 360582661033156140, 360582660507654674, 360582660624799090]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582764328992013, 360582778622558090⟩, ⟨(-6041808598560634), (-5579928294370344)⟩, true⟩

def words01 : List Nat := [360582660625384825, 360582660614431625, 360582660925125705, 360582661528232495, 360582661945006990, 360582662361871592, 360582662365732613, 360582662366390348, 360582661935729345, 360582661938919221]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360548949437772618, 360548963737532920⟩, ⟨1611051914614066080, 1611514091157462636⟩, true⟩

def words02 : List Nat := [360582661939452949, 360582661862427949, 360582661348485121, 360582660566108620, 360582659783646505, 360582658887584368, 360582658214358632, 360582657653349005, 360582657092286622, 360582656275504015]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566773701731407, 360566788007710054⟩, ⟨758314453234452312, 758776927232028232⟩, true⟩

def words03 : List Nat := [360582655571637169, 360582654857608071, 360582654143416484, 360582653689976938, 360582652799873231, 360582651540926825, 360582650281907099, 360582649458901913, 360582649060291698, 360582648729433132]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558203896169219, 360558218208410481⟩, ⟨1168177750012700525, 1168640523644006235⟩, true⟩

def words04 : List Nat := [360582648398489639, 360582647780453609, 360582646977586468, 360582646610613212, 360582646243483256, 360582645572763134, 360582644615443938, 360582643383499864, 360582642151481371, 360582641207859677]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk478A
