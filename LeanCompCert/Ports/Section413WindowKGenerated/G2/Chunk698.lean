import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk698

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

def state06 : KState := ⟨⟨360578883011751951, 360578914461530352⟩, ⟨256338872957343763, 257822925985123049⟩, true⟩

def words05 : List Nat := [360582607770840716, 360582607614500709, 360582607457891217, 360582607209056175, 360582606820540282, 360582606257416245, 360582605694118253, 360582605335524280, 360582605079106096, 360582605027318860]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566681944190136, 360566713403385197⟩, ⟨1108634554568142752, 1110119265489346540⟩, true⟩

def words06 : List Nat := [360582604975379675, 360582604752683146, 360582604470660945, 360582604279339024, 360582604087760029, 360582603810822172, 360582603372952234, 360582602779007213, 360582602184889855, 360582601756977431]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561327167681287, 360561358636192012⟩, ⟨1482879972384192671, 1484365334237285279⟩, true⟩

def words07 : List Nat := [360582601530381756, 360582601468197928, 360582601405901386, 360582601241494100, 360582601170703121, 360582600970289114, 360582600772337221, 360582600773326546, 360582600572434300, 360582600269481041]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566945036411227, 360566976514275999⟩, ⟨1090216814680715585, 1091702830241622591⟩, true⟩

def words08 : List Nat := [360582599966326397, 360582599604598558, 360582599368391409, 360582599164506079, 360582598960558238, 360582598582390962, 360582598053142591, 360582597594355716, 360582597135267722, 360582596815180873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360560087993329504, 360560119480609127⟩, ⟨1569492635046705930, 1570979308658887212⟩, true⟩

def words09 : List Nat := [360582596592567340, 360582596267931159, 360582595943115118, 360582595738081243, 360582595691946529, 360582595503199743, 360582595314351779, 360582594994097638, 360582594469230814, 360582594148830285]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk698
