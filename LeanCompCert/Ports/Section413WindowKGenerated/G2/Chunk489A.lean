import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk489A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360550497361380129, 360550512335199466⟩, ⟨1540759182904528501, 1541253961685198475⟩, true⟩

def state01 : KState := ⟨⟨360579743385057102, 360579758365231220⟩, ⟨110495098191095055, 110990187751204451⟩, true⟩

def words00 : List Nat := [360582030177131550, 360582029842776143, 360582029527519992, 360582029003981961, 360582028480355465, 360582027852573140, 360582027724908426, 360582027869884272, 360582027870496409, 360582027639157845]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589597709834129, 360589612696363737⟩, ⟨(-371497484927626413), (-371002084488578765)⟩, true⟩

def words01 : List Nat := [360582027824260054, 360582028055946171, 360582028532793739, 360582028773279415, 360582028773906424, 360582028660915819, 360582028547792864, 360582028687177114, 360582028842753545, 360582028998473494]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561981714199414, 360561996707157302⟩, ⟨979373871181172901, 979869586122237821⟩, true⟩

def words02 : List Nat := [360582028999074686, 360582028887332346, 360582028494536080, 360582027954968795, 360582027415239386, 360582026652695550, 360582025758267778, 360582024612214833, 360582023466075182, 360582022654145290]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360514256422204656, 360514271421503645⟩, ⟨3314968274933179242, 3315464300177261482⟩, true⟩

def words03 : List Nat := [360582022245421243, 360582022172637657, 360582022099785803, 360582021815825736, 360582021281760457, 360582020643821324, 360582020005720093, 360582019359245759, 360582018295490119, 360582016911903671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557008735221990, 360557023740887512⟩, ⟨1222423374188862076, 1222919711042119806⟩, true⟩

def words04 : List Nat := [360582015528221109, 360582014478722331, 360582013636999193, 360582012938452864, 360582012239871373, 360582011181565708, 360582009706038325, 360582008646820305, 360582007587448346, 360582006778906759]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk489A
