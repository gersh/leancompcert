import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk965A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605702446916665, 360605763990521914⟩, ⟨(-2268839630948301777), (-2264829389010748867)⟩, true⟩

def state01 : KState := ⟨⟨360589693849597723, 360589755406544315⟩, ⟨(-723959779171197303), (-719948249727303731)⟩, true⟩

def words00 : List Nat := [360582294679038888, 360582294883804649, 360582295077220544, 360582295271035098, 360582295437061366, 360582295523210343, 360582295555607704, 360582295588147631, 360582295589302154, 360582295653254770]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584646479165901, 360584708049298257⟩, ⟨(-236760802856625249), (-232748000789585755)⟩, true⟩

def words01 : List Nat := [360582295814215587, 360582295975449434, 360582296074732600, 360582296197460242, 360582296277256329, 360582296357463695, 360582296544606165, 360582296625004676, 360582296651235581, 360582296677671466]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611159646662808, 360611221230029733⟩, ⟨(-2795982330039512957), (-2791968250508552895)⟩, true⟩

def words02 : List Nat := [360582296792647501, 360582296961460846, 360582297127316046, 360582297293416800, 360582297355463714, 360582297392051983, 360582297535730997, 360582297679818382, 360582297906783808, 360582298207886499]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609123196306320, 360609184793005514⟩, ⟨(-2599407725547456185), (-2595392358986790225)⟩, true⟩

def words03 : List Nat := [360582298439590123, 360582298671440134, 360582298965000911, 360582299319604748, 360582299628846743, 360582299938319980, 360582300165152746, 360582300397862205, 360582300677475937, 360582300957547141]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595932552689812, 360595994162565547⟩, ⟨(-1325937244932737119), (-1321920606240456533)⟩, true⟩

def words04 : List Nat := [360582301294782925, 360582301525318768, 360582301680237401, 360582301835315121, 360582301962740370, 360582302143919610, 360582302312504063, 360582302481345665, 360582302596056988, 360582302739315240]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk965A
