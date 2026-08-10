import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk887A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578755669149468, 360578807326492446⟩, ⟨288841171327335047, 291935363678319741⟩, true⟩

def state01 : KState := ⟨⟨360574171366527169, 360574223036041439⟩, ⟨695390836044980091, 698486108051632963⟩, true⟩

def words00 : List Nat := [360582098557309710, 360582098457828906, 360582098231176732, 360582098106357094, 360582097981153488, 360582097810637230, 360582097598058411, 360582097321986577, 360582097045676141, 360582096850809241]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360545066644641277, 360545118326211111⟩, ⟨3277364560981536835, 3280460902499230757⟩, true⟩

def words01 : List Nat := [360582096763107648, 360582096583370779, 360582096403503150, 360582096160605446, 360582095790613666, 360582095339036389, 360582094887093761, 360582094532168524, 360582094180143644, 360582093764697352]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583642283717320, 360583693977362365⟩, ⟨(-145279106278074207), (-142181693391069279)⟩, true⟩

def words02 : List Nat := [360582093348970316, 360582093060454777, 360582092849244361, 360582092673740333, 360582092498168110, 360582092206526826, 360582091940758122, 360582091774727496, 360582091608324930, 360582091587065952]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578778747608126, 360578830453463297⟩, ⟨286315829721997499, 289414326072323825⟩, true⟩

def words03 : List Nat := [360582091588216159, 360582091544458254, 360582091551819150, 360582091685310472, 360582091786549801, 360582091887996268, 360582091893072599, 360582091894357806, 360582091862707208, 360582091827433010]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587488302232445, 360587540020125953⟩, ⟨(-486639006317490043), (-483539441623645965)⟩, true⟩

def words04 : List Nat := [360582091881717510, 360582091882996621, 360582091847309127, 360582091748176392, 360582091648837177, 360582091517975711, 360582091577172463, 360582091670907090, 360582091687063336, 360582091749778311]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk887A
