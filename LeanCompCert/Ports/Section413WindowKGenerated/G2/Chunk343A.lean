import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk343A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585920069613239, 360585927225815683⟩, ⟨(-153433773718270179), (-153267819166267367)⟩, true⟩

def state01 : KState := ⟨⟨360624699277469670, 360624706438005466⟩, ⟨(-1483575137583183249), (-1483409034375245185)⟩, true⟩

def words00 : List Nat := [360581459886002435, 360581461292003234, 360581463546556085, 360581465801065432, 360581467331230063, 360581468591660070, 360581469341739309, 360581470091905342, 360581470965819613, 360581472226400580]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360637078729833476, 360637085894745809⟩, ⟨(-1908343648768939197), (-1908177395380917685)⟩, true⟩

def words01 : List Nat := [360581473059331703, 360581473892264523, 360581475573332588, 360581477961863060, 360581480135136809, 360581482308359561, 360581483926702821, 360581484699305571, 360581486319758713, 360581487940275342]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360620549412921192, 360620556582162237⟩, ⟨(-1341144673368859568), (-1340978271396825396)⟩, true⟩

def words02 : List Nat := [360581489533718778, 360581490412396706, 360581490707317133, 360581491002269604, 360581491070060791, 360581491566190538, 360581492909781596, 360581494253390239, 360581495169761173, 360581496308025253]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360626778182900236, 360626785356479590⟩, ⟨(-1555202905252075480), (-1555036354324670698)⟩, true⟩

def words03 : List Nat := [360581497570412217, 360581498832857666, 360581499952860453, 360581500227963086, 360581500228398155, 360581499729326709, 360581499577868065, 360581500508828295, 360581501827920775, 360581503147041174]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360641832529055036, 360641839707018990⟩, ⟨(-2072297822546857627), (-2072131121030653441)⟩, true⟩

def words04 : List Nat := [360581504039282172, 360581505422863862, 360581507375501922, 360581509328166074, 360581511066046768, 360581512559755806, 360581513603458862, 360581514647151787, 360581515656391494, 360581517413023746]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk343A
