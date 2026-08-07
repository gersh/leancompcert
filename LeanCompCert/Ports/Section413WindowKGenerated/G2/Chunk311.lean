import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk311

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360630567437147357, 360630573272458637⟩, ⟨(-1481713696904347870), (-1481590972552646806)⟩, true⟩

def state01 : KState := ⟨⟨360583686433335702, 360583692272589905⟩, ⟨(-23793637183621409), (-23670790187522449)⟩, true⟩

def words00 : List Nat := [360582935948027417, 360582935948440813, 360582935790990388, 360582935940385997, 360582935940732061, 360582935829351393, 360582935030089498, 360582933717610679, 360582932405128957, 360582931423045130]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360490857444902201, 360490863288046027⟩, ⟨2864810835608873769, 2864933803631027317⟩, true⟩

def words01 : List Nat := [360582932127391023, 360582932831770635, 360582933008385904, 360582933008799605, 360582932548928497, 360582931338357777, 360582930127744385, 360582929129257987, 360582927100839219, 360582924142918490]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360562265325726165, 360562271172782195⟩, ⟨642412645001483461, 642535734789667829⟩, true⟩

def words02 : List Nat := [360582921185094472, 360582919255599316, 360582918170956308, 360582918114399201, 360582918057813597, 360582917132507395, 360582915492138174, 360582914195323828, 360582912898477578, 360582911575441677]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360547886013349234, 360547891864344317⟩, ⟨1090119831481574687, 1090243043912176263⟩, true⟩

def words03 : List Nat := [360582910912796387, 360582909732832187, 360582908552864572, 360582908226940006, 360582908227287964, 360582907752542197, 360582907277774762, 360582906155407143, 360582904004396709, 360582902880526468]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360549226611815179, 360549232466715244⟩, ⟨1048094001810859912, 1048217335862066338⟩, true⟩

def words04 : List Nat := [360582901756590227, 360582900300974153, 360582898377678431, 360582895650309830, 360582892923047816, 360582889936091278, 360582887589418406, 360582886269422482, 360582884949467641, 360582883103500544]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360616492898374149, 360616498757180076⟩, ⟨(-1047589089122150621), (-1047465633383927089)⟩, true⟩

def words05 : List Nat := [360582882023592878, 360582881970126509, 360582882888802977, 360582883314082730, 360582883314464828, 360582882855417586, 360582882396326434, 360582881964047710, 360582883043227194, 360582884122432028]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360548300176635315, 360548306039385396⟩, ⟨1077293387041572044, 1077416965699375150⟩, true⟩

def words06 : List Nat := [360582884417586180, 360582884418000492, 360582883686076548, 360582883113560120, 360582882540963429, 360582881400520480, 360582879233215830, 360582876540887011, 360582873848651848, 360582871870816239]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360542800888253312, 360542806754913137⟩, ⟨1248647683292546155, 1248771383836342095⟩, true⟩

def words07 : List Nat := [360582870762247422, 360582869356903622, 360582867951604842, 360582866035079546, 360582864474695638, 360582862331008346, 360582860187333184, 360582859068411898, 360582858436187758, 360582857152085567]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620920452653262, 360620926323224016⟩, ⟨(-1187440827858055554), (-1187317005352380288)⟩, true⟩

def words08 : List Nat := [360582855867972148, 360582855868355787, 360582857152902457, 360582858437446014, 360582858652645330, 360582858653060261, 360582858277772277, 360582858207240604, 360582859089535839, 360582860310420567]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598772725115632, 360598778599641704⟩, ⟨(-496471249320935050), (-496347303429096856)⟩, true⟩

def words09 : List Nat := [360582860866651530, 360582861422899014, 360582863002799944, 360582865095664404, 360582866562362819, 360582868029036669, 360582868984566870, 360582869521501106, 360582870031748735, 360582870542097744]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk311
