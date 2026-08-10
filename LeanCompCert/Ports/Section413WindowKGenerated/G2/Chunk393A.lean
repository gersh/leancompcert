import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk393A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591111140741248, 360591120640643767⟩, ⟨(-347133981312706075), (-346881635606540629)⟩, true⟩

def state01 : KState := ⟨⟨360582430162618542, 360582439667524330⟩, ⟨(-5929978829711750), (-5677436469168638)⟩, true⟩

def words00 : List Nat := [360582295231558425, 360582295708816952, 360582295709298290, 360582295688473106, 360582295667568556, 360582295206031845, 360582295233076045, 360582295398261375, 360582295398735234, 360582295243915947]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622308533211191, 360622318043146409⟩, ⟨(-1573710448552178626), (-1573457708459785334)⟩, true⟩

def words01 : List Nat := [360582295526876156, 360582295809995695, 360582296738545579, 360582297569679515, 360582297847941840, 360582298126231645, 360582299049946940, 360582300297340704, 360582301315523943, 360582302333768220]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615314725662997, 360615324240670662⟩, ⟨(-1298939614835729715), (-1298686675270910261)⟩, true⟩

def words02 : List Nat := [360582302889546136, 360582302890078304, 360582303360381953, 360582303918581754, 360582303945155508, 360582304087548290, 360582304088022344, 360582303907021049, 360582303983883666, 360582304824045840]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598399227040057, 360598408747067886⟩, ⟨(-633566460578613202), (-633313323546027970)⟩, true⟩

def words03 : List Nat := [360582306034343031, 360582307244680318, 360582307956457116, 360582308231942803, 360582308343501280, 360582308455198773, 360582309079992132, 360582309879164342, 360582310288867751, 360582310698631242]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360623626115361678, 360623635640409595⟩, ⟨(-1625944210652501629), (-1625690876104871799)⟩, true⟩

def words04 : List Nat := [360582311752964425, 360582313177366308, 360582315246227550, 360582317315085532, 360582318799954044, 360582319836613873, 360582320491872671, 360582321147248936, 360582322021659498, 360582323072085922]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk393A
