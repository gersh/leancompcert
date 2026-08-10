import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk698A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360564782752672141, 360564814146303951⟩, ⟨1241758217157219978, 1243238349473404790⟩, true⟩

def state01 : KState := ⟨⟨360573004547896203, 360573035950944600⟩, ⟨667691499561682916, 669172289200487464⟩, true⟩

def words00 : List Nat := [360582625329681782, 360582624957354696, 360582624518016555, 360582624158683454, 360582623799070765, 360582623328181744, 360582622914998504, 360582622399518161, 360582621883863370, 360582621573193569]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360542707419074296, 360542738831436435⟩, ⟨2782901229274470291, 2784382669153742395⟩, true⟩

def words01 : List Nat := [360582621436698493, 360582621296517579, 360582621156240454, 360582620913300429, 360582620529839327, 360582620095304973, 360582619660498464, 360582619249340063, 360582618844007701, 360582618273847689]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568377099458208, 360568408521151717⟩, ⟨990502564485893292, 991984655926031478⟩, true⟩

def words02 : List Nat := [360582617703480022, 360582617337992211, 360582617078690377, 360582616800598267, 360582616522456506, 360582616064259918, 360582615401028609, 360582614942653431, 360582614483992453, 360582614230100966]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360550740005023456, 360550771436152126⟩, ⟨2222283796547618342, 2223766546891337280⟩, true⟩

def words03 : List Nat := [360582614027560210, 360582613722482506, 360582613417205763, 360582613328159276, 360582613328986691, 360582613290087597, 360582613251074373, 360582613109817785, 360582612763596602, 360582612308816665]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564838076743806, 360564869517184359⟩, ⟨1237551299491808392, 1239034700223724060⟩, true⟩

def words04 : List Nat := [360582611853710897, 360582611563582244, 360582611136750251, 360582610595393173, 360582610053888451, 360582609425260778, 360582608952782625, 360582608684944689, 360582608417019952, 360582608023987849]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk698A
