import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk659A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360608946257194079, 360608974113018297⟩, ⟨(-1716826011338123937), (-1715585990264906661)⟩, true⟩

def state01 : KState := ⟨⟨360587087147229963, 360587115011896054⟩, ⟨(-276322830353592803), (-275082226557269349)⟩, true⟩

def words00 : List Nat := [360582941556036716, 360582941605066714, 360582941810590564, 360582942016380526, 360582942057490153, 360582942058419902, 360582941962365921, 360582941751590888, 360582941540646496, 360582941471416358]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360555042341554918, 360555070214980982⟩, ⟨1835958554837916926, 1837199736047982078⟩, true⟩

def words01 : List Nat := [360582941635605721, 360582941799988898, 360582941835054639, 360582941835983779, 360582941641461447, 360582941389571315, 360582941137407506, 360582941009567917, 360582940778439761, 360582940356607924]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604793476841104, 360604821359038053⟩, ⟨(-1443948004489368487), (-1442706245059131615)⟩, true⟩

def words02 : List Nat := [360582939934578447, 360582939742593975, 360582939665515053, 360582939513981133, 360582939362388602, 360582939018201240, 360582938775021396, 360582938761852834, 360582938963942984, 360582939296805430]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595096303347350, 360595124194409446⟩, ⟨(-804571606092793773), (-803329262141028975)⟩, true⟩

def words03 : List Nat := [360582939514387450, 360582939732064405, 360582939944158508, 360582940354284049, 360582940706569746, 360582941059000735, 360582941282707081, 360582941283636619, 360582941462634246, 360582941648464723]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360562140036767139, 360562167936580705⟩, ⟨1368679979550123803, 1369922900617639069⟩, true⟩

def words04 : List Nat := [360582941844304058, 360582941845233670, 360582941811783817, 360582941616012638, 360582941420101191, 360582941072297928, 360582940869770923, 360582940662055849, 360582940454251660, 360582940080638592]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk659A
