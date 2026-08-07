import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk478

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

def state06 : KState := ⟨⟨360517527675433387, 360517541993875609⟩, ⟨3114854947651945532, 3115318018030626142⟩, true⟩

def words05 : List Nat := [360582640697995033, 360582640536566685, 360582640375070040, 360582639936462760, 360582639209263765, 360582638214440348, 360582637219465623, 360582636660087004, 360582635664562804, 360582634305159158]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565680371149088, 360565694695804592⟩, ⟨809901426228583436, 810364794006331470⟩, true⟩

def words06 : List Nat := [360582632945667990, 360582631463574519, 360582630203743331, 360582629145240608, 360582628086730226, 360582626654131707, 360582625411276167, 360582624510342195, 360582623609252933, 360582623143559059]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360536333604890770, 360536347935835147⟩, ⟨2214913394038218266, 2215377062893801902⟩, true⟩

def words07 : List Nat := [360582622790525364, 360582622220044189, 360582621649463973, 360582621059752758, 360582620735893654, 360582620287667023, 360582619839387159, 360582619173864546, 360582618263659606, 360582617298050975]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360521560270978670, 360521574608118626⟩, ⟨2922360424315387215, 2922824389847032245⟩, true⟩

def words08 : List Nat := [360582616332242761, 360582615801612372, 360582614966688336, 360582613796250828, 360582612625754885, 360582611266401564, 360582610195850441, 360582609115038988, 360582608034207361, 360582606647998498]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580551783222943, 360580566126582363⟩, ⟨96963730387384936, 97427993799599610⟩, true⟩

def words09 : List Nat := [360582605374136456, 360582604428052487, 360582603481811735, 360582602829347330, 360582602410302900, 360582601623610985, 360582600836825769, 360582600386758924, 360582600155708049, 360582600113926823]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk478
