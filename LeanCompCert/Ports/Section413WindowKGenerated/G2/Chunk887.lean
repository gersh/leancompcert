import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk887

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

def state06 : KState := ⟨⟨360574139569180838, 360574191299166005⟩, ⟨698104987097832872, 701205624986581670⟩, true⟩

def words05 : List Nat := [360582091850111062, 360582091950812981, 360582092019038686, 360582092020317983, 360582091989222835, 360582091836654906, 360582091683849595, 360582091512608459, 360582091405131363, 360582091317473651]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555690928922199, 360555742671087244⟩, ⟨2335602717373317422, 2338704436407855208⟩, true⟩

def words06 : List Nat := [360582091229610312, 360582091078344106, 360582090800062761, 360582090596781989, 360582090393160179, 360582090128815346, 360582089737599530, 360582089246425881, 360582088755016108, 360582088333320069]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545928866358289, 360545980620566483⟩, ⟨3202318639188538106, 3205421427353963374⟩, true⟩

def words07 : List Nat := [360582088037572088, 360582087868737159, 360582087699766587, 360582087459165222, 360582087274320619, 360582087030130752, 360582086785560709, 360582086579157506, 360582086245878403, 360582085840518657]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557747967775259, 360557799734078747⟩, ⟨2152890883427154764, 2155994745472108510⟩, true⟩

def words08 : List Nat := [360582085434901012, 360582084964136015, 360582084556675461, 360582084236749231, 360582083916740862, 360582083487380997, 360582082963835947, 360582082496724765, 360582082029223141, 360582081688639758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556790605867347, 360556842384351272⟩, ⟨2237880113190218313, 2240985056797193197⟩, true⟩

def words09 : List Nat := [360582081416310036, 360582081056525555, 360582080696495174, 360582080463466623, 360582080294171314, 360582080015668991, 360582079737033245, 360582079395048068, 360582078985291542, 360582078702558448]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk887
