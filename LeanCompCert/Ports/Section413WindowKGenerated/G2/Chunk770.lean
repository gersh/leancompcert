import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk770

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585877274931362, 360585915777452340⟩, ⟨(-291037075784716973), (-289034702084464375)⟩, true⟩

def state01 : KState := ⟨⟨360577257218082261, 360577295731051340⟩, ⟨372642442624641942, 374645620879234386⟩, true⟩

def words00 : List Nat := [360582162129749885, 360582162095338839, 360582161892490324, 360582161858321083, 360582161823846585, 360582161747372661, 360582161539182195, 360582161196432069, 360582160853480776, 360582160626790585]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564495013720840, 360564533537026090⟩, ⟨1355543898222424102, 1357547872518970998⟩, true⟩

def words01 : List Nat := [360582160564513196, 360582160529216140, 360582160493804681, 360582160362311147, 360582160235169615, 360582160041538054, 360582159847589140, 360582159822124402, 360582159678431956, 360582159450717586]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585043994405206, 360585082528101787⟩, ⟨(-227247153225040395), (-225242378538587191)⟩, true⟩

def words02 : List Nat := [360582159222775669, 360582158991332590, 360582158953324904, 360582159019096111, 360582159020115476, 360582158940403424, 360582158787984757, 360582158616611310, 360582158444898465, 360582158479620805]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360572194436584383, 360572232980746930⟩, ⟨762589346168003016, 764594927099238972⟩, true⟩

def words03 : List Nat := [360582158480609901, 360582158433596391, 360582158386380053, 360582158350585337, 360582158351521796, 360582158257546421, 360582158163453774, 360582157985349759, 360582157756894475, 360582157629333369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588714678450741, 360588753232975049⟩, ⟨(-510207699173319410), (-508201319920166812)⟩, true⟩

def words04 : List Nat := [360582157540746315, 360582157585670175, 360582157586649489, 360582157530291981, 360582157473748304, 360582157336486262, 360582157397263692, 360582157512380843, 360582157513386451, 360582157584379701]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360606630133776216, 360606668698671090⟩, ⟨(-1890747840067282819), (-1888740661709596709)⟩, true⟩

def words05 : List Nat := [360582157721524918, 360582157858984899, 360582158086541569, 360582158202072481, 360582158203093070, 360582158156865946, 360582158199544917, 360582158377775791, 360582158696732474, 360582159015930020]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603288151472906, 360603326726853893⟩, ⟨(-1633369671185493183), (-1631361684717158089)⟩, true⟩

def words06 : List Nat := [360582159217162482, 360582159304676296, 360582159354117077, 360582159403871956, 360582159411214882, 360582159443660834, 360582159444649561, 360582159391909268, 360582159453167110, 360582159729089272]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569296512938653, 360569335098669263⟩, ⟨986597462703564722, 988606246869196354⟩, true⟩

def words07 : List Nat := [360582160101898737, 360582160474908648, 360582160742253692, 360582160885895370, 360582160986070709, 360582161086545103, 360582161087460242, 360582161062037482, 360582160980674438, 360582160815416399]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599963115717471, 360600001711824906⟩, ⟨(-1377336924230036177), (-1375327340167228405)⟩, true⟩

def words08 : List Nat := [360582160651515933, 360582160759182325, 360582160941098064, 360582161123236933, 360582161158604018, 360582161159703551, 360582161029876310, 360582161033822455, 360582161169234023, 360582161401799518]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592071479175735, 360592110085766902⟩, ⟨(-768915910736053597), (-766905518429762035)⟩, true⟩

def words09 : List Nat := [360582161504316720, 360582161606934117, 360582161877272135, 360582162231685712, 360582162485308831, 360582162739103822, 360582162897671387, 360582163060717209, 360582163190627299, 360582163320894466]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk770
