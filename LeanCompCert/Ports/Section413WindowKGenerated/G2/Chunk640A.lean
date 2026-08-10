import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk640A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604511481809492, 360604537693059095⟩, ⟨(-1391293761420655910), (-1390160563574128470)⟩, true⟩

def state01 : KState := ⟨⟨360604685459062587, 360604711678819271⟩, ⟨(-1402455135760282407), (-1401321393418704205)⟩, true⟩

def words00 : List Nat := [360582817026488585, 360582817401078902, 360582817906102394, 360582818411281824, 360582818676561603, 360582818699057552, 360582818965292884, 360582819231810531, 360582819451775078, 360582819794714685]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360599761782174238, 360599788010500939⟩, ⟨(-1087262920838958614), (-1086128629888263028)⟩, true⟩

def words01 : List Nat := [360582819991727746, 360582820188835440, 360582820629640094, 360582821221638074, 360582821610130425, 360582821998743718, 360582822263524562, 360582822285596021, 360582822551330778, 360582822817362934]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615678429105924, 360615704665922116⟩, ⟨(-2106294358970759602), (-2105159524480449530)⟩, true⟩

def words02 : List Nat := [360582823262894558, 360582823821282674, 360582824256854880, 360582824692511991, 360582824991905807, 360582825414715890, 360582825991758119, 360582826568954480, 360582826958842661, 360582827473242314]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360639874042041743, 360639900287357559⟩, ⟨(-3655714195594674508), (-3654578816831005370)⟩, true⟩

def words03 : List Nat := [360582828024847755, 360582828576697460, 360582829371978275, 360582829991735862, 360582830399317466, 360582830806964420, 360582831458102453, 360582832267505559, 360582833159366669, 360582834051401984]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360634259656023119, 360634285909928641⟩, ⟨(-3296232781641617678), (-3295096852752696276)⟩, true⟩

def words04 : List Nat := [360582834820688383, 360582835659845920, 360582836491016725, 360582837322423039, 360582838091969795, 360582838715848913, 360582839179474960, 360582839643184447, 360582840212508143, 360582841016753629]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk640A
