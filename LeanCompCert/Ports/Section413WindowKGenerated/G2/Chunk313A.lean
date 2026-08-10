import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk313A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360492178128328244, 360492184042146007⟩, ⟨2838689953515238052, 2838815127273140154⟩, true⟩

def state01 : KState := ⟨⟨360593981318146541, 360593987235892656⟩, ⟨(-348296384841389035), (-348171088106659609)⟩, true⟩

def words00 : List Nat := [360582878113831003, 360582876015433780, 360582874629894482, 360582873708453104, 360582872787028831, 360582870993019474, 360582869071263854, 360582868166618090, 360582867261908437, 360582867466862390]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360614139735258793, 360614145656980309⟩, ⟨(-979668023883918387), (-979542602660555809)⟩, true⟩

def words01 : List Nat := [360582867467243316, 360582866990311728, 360582866829437518, 360582867866142866, 360582868644703625, 360582869423282595, 360582869423657848, 360582869368283965, 360582870349902182, 360582871348923078]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360625986073890199, 360625991999532014⟩, ⟨(-1350857995779741698), (-1350732451752998274)⟩, true⟩

def words02 : List Nat := [360582873363600130, 360582874360848745, 360582874788081118, 360582875215331796, 360582875215686880, 360582875313811446, 360582876721901057, 360582878129983221, 360582878930099450, 360582880306584040]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360617626394283939, 360617632323862750⟩, ⟨(-1088930807381920126), (-1088805139989185764)⟩, true⟩

def words03 : List Nat := [360582881448630754, 360582882590732685, 360582884747952272, 360582885888190210, 360582886158048395, 360582886427922032, 360582887712865437, 360582889506149152, 360582890615071944, 360582891724009868]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577935343071005, 360577941276620103⟩, ⟨154933563174384981, 155059355014771089⟩, true⟩

def words04 : List Nat := [360582892242101301, 360582892242518136, 360582891744009154, 360582891547573595, 360582891351040419, 360582890897124860, 360582890481192397, 360582889470965996, 360582888460724162, 360582887348550399]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk313A
