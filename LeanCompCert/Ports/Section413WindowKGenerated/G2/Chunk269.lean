import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk269

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360669994067517452, 360669998378975845⟩, ⟨(-2352125019726470393), (-2352046570691989639)⟩, true⟩

def state01 : KState := ⟨⟨360666314213051249, 360666318527884813⟩, ⟨(-2253507761265338214), (-2253429221422862206)⟩, true⟩

def words00 : List Nat := [360582567081262074, 360582567832588387, 360582569963195566, 360582572093748445, 360582573865845403, 360582575450196020, 360582576339087343, 360582577227957368, 360582579054364717, 360582582166492711]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562069243542201, 360562073561702454⟩, ⟨552350624801539183, 552429254182416217⟩, true⟩

def words01 : List Nat := [360582585733679090, 360582589300667387, 360582592172817137, 360582593669992436, 360582594217305441, 360582594764666019, 360582595521901392, 360582595522255230, 360582595469809407, 360582594707845932]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598786248494159, 360598790569999756⟩, ⟨(-436112263766920148), (-436033544312805842)⟩, true⟩

def words02 : List Nat := [360582594560849784, 360582596243708250, 360582597721371788, 360582599198991235, 360582599480071245, 360582599480425039, 360582598671614576, 360582598955874881, 360582599201482439, 360582599803065264]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360537249656926017, 360537253981799957⟩, ⟨1221533933302129777, 1221612743482626239⟩, true⟩

def words03 : List Nat := [360582599803380730, 360582599594464789, 360582599797910096, 360582601026306834, 360582601897715826, 360582602769125566, 360582602769444054, 360582602745657470, 360582601349282774, 360582599666413270]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556739641599685, 360556743969814643⟩, ⟨696181005782276737, 696259905986098669⟩, true⟩

def words04 : List Nat := [360582597983552208, 360582597016854393, 360582595479895692, 360582592878345528, 360582590276931741, 360582586851007045, 360582584126901698, 360582582777850637, 360582581428862721, 360582579216790009]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360616264709923112, 360616269041474528⟩, ⟨(-908334080539682081), (-908255090401064491)⟩, true⟩

def words05 : List Nat := [360582578674496170, 360582579090875459, 360582580881568474, 360582581301290044, 360582581301619662, 360582580523343233, 360582579745061481, 360582578928371171, 360582580054075379, 360582581303987007]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360622370347297921, 360622374682225210⟩, ⟨(-1073216801759861430), (-1073137720591839044)⟩, true⟩

def words06 : List Nat := [360582581367535591, 360582581844311117, 360582583207838262, 360582584571377901, 360582585578497174, 360582585713971835, 360582585714287796, 360582585015003243, 360582584629147739, 360582586104842398]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360549174197748481, 360549178536020073⟩, ⟨901184504444265404, 901263675824633006⟩, true⟩

def words07 : List Nat := [360582587542655813, 360582588980427675, 360582589541972160, 360582589542326678, 360582588735027532, 360582587115435862, 360582585495860894, 360582584796264508, 360582584654330822, 360582583416517651]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360621596454088196, 360621600795704904⟩, ⟨(-1053130853035374637), (-1053051591386892111)⟩, true⟩

def words08 : List Nat := [360582582311965109, 360582583140055729, 360582584041789318, 360582584943521803, 360582584943854415, 360582584533585982, 360582583281387439, 360582583340922981, 360582584434041627, 360582585879940876]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583789541413060, 360583793886415271⟩, ⟨(-32279532423895428), (-32200179384290142)⟩, true⟩

def words09 : List Nat := [360582586638670675, 360582587397386013, 360582589526046962, 360582592702595176, 360582595524625400, 360582598346505220, 360582600477711114, 360582601242305174, 360582601286770136, 360582601331347523]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk269
