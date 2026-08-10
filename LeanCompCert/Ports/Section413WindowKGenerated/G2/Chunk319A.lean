import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk319A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360486270012567769, 360486276165098816⟩, ⟨3062241796811480445, 3062374514137382131⟩, true⟩

def state01 : KState := ⟨⟨360558496526932553, 360558502683469931⟩, ⟨757786303405814414, 757919148553755030⟩, true⟩

def words00 : List Nat := [360582272357228767, 360582269235192592, 360582266736877062, 360582264910321389, 360582263083850665, 360582260422866327, 360582258116453341, 360582256788059834, 360582255459626294, 360582254458730156]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360495501541388552, 360495507701977886⟩, ⟨2768214212478553866, 2768347186944265210⟩, true⟩

def words01 : List Nat := [360582253714798079, 360582252211995285, 360582250709211570, 360582248889761560, 360582247559757297, 360582245680890888, 360582243802095862, 360582241434615992, 360582238087365575, 360582235370741805]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360506659988316259, 360506666152906909⟩, ⟨2412014819400486736, 2412147921608477498⟩, true⟩

def words02 : List Nat := [360582232654138538, 360582230671756331, 360582228559591356, 360582225951428271, 360582223343359154, 360582220469818693, 360582218283729909, 360582216073178662, 360582213862717918, 360582211029875543]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360548385214229837, 360548391382830496⟩, ⟨1079487641335696231, 1079620871603792449⟩, true⟩

def words03 : List Nat := [360582208664340806, 360582206855152652, 360582205045951475, 360582203389835496, 360582201767961935, 360582199305508090, 360582196843127238, 360582195158625564, 360582193970812247, 360582192912937065]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360490475665690454, 360490481838351777⟩, ⟨2929088774726782022, 2929222134711748974⟩, true⟩

def words04 : List Nat := [360582191855079249, 360582190002584917, 360582187171764516, 360582184669116470, 360582182166509636, 360582179420543035, 360582175696463125, 360582171353637721, 360582167010995636, 360582163282317716]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk319A
