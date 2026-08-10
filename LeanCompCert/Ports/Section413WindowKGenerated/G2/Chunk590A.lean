import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk590A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360601068489874733, 360601090622024435⟩, ⟨(-1126429727545644697), (-1125547543745811581)⟩, true⟩

def state01 : KState := ⟨⟨360576199435392384, 360576221575402336⟩, ⟨340770387850204110, 341653035443162248⟩, true⟩

def words00 : List Nat := [360582014024944677, 360582014025768962, 360582013895898605, 360582013757868448, 360582013619609822, 360582013407573084, 360582012980937558, 360582012332684982, 360582011684296346, 360582011323503390]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360542803465561864, 360542825613330304⟩, ⟨2311737058958884282, 2312620164419337230⟩, true⟩

def words01 : List Nat := [360582011415220946, 360582011605203220, 360582011630665034, 360582011631491287, 360582011532996250, 360582011173140066, 360582010813065646, 360582010444815762, 360582009945728406, 360582009282669839]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601194301032479, 360601216456580877⟩, ⟨(-1134765630421032704), (-1133882065747991968)⟩, true⟩

def words02 : List Nat := [360582008619442708, 360582008243667420, 360582008064482668, 360582008118985157, 360582008119746287, 360582007927900732, 360582007694017405, 360582007661591005, 360582007882700841, 360582008208952547]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587882139871310, 360587904303289506⟩, ⟨(-348950666139956217), (-348066636873426099)⟩, true⟩

def words03 : List Nat := [360582008311132653, 360582008413380091, 360582008472455777, 360582008674425127, 360582008802414153, 360582008930533615, 360582008931273213, 360582008844687234, 360582008864723278, 360582008965526369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573714997391125, 360573737168575115⟩, ⟨487461186051912311, 488345673849306825⟩, true⟩

def words04 : List Nat := [360582009022631511, 360582009023456667, 360582008892869103, 360582008617812525, 360582008342641997, 360582007863720986, 360582007567937353, 360582007494905473, 360582007421787728, 360582007205388821]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk590A
