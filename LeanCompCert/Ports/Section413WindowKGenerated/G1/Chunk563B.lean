import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk563A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk563B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk563A

def state06 : KState := ⟨⟨362490572343484350, 362490618685787288⟩, ⟨(-323527207294862440), (-321762834790818682)⟩, true⟩

def words05 : List Nat := [371284909956644808, 371284910043297089, 371284910248670258, 371284910250572370, 371284910129847094, 371284909967401151, 371284909804229495, 371284909730577459, 371284909619855901, 371284909723299206]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477671171794058, 362477717531220306⟩, ⟨403582367371397357, 405347705032394445⟩, true⟩

def words06 : List Nat := [371284909825925302, 371284909827823506, 371284909510946072, 371284909475000591, 371284909495709152, 371284909497607624, 371284909137367036, 371284908777719651, 371284908417278963, 371284908372182386]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463690571930636, 362463736948454267⟩, ⟨1191751177128065921, 1193517478654508997⟩, true⟩

def words07 : List Nat := [371284908248319205, 371284908252756126, 371284908254181521, 371284908228152054, 371284907826571619, 371284907400077811, 371284906972573805, 371284906860090239, 371284906486038095, 371284906112673042]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478141659517225, 362478188053025963⟩, ⟨376986538982161243, 378753798215790087⟩, true⟩

def words08 : List Nat := [371284905738501508, 371284905573536860, 371284905250610146, 371284905242793068, 371284905234398346, 371284905149329316, 371284904787587716, 371284904721139567, 371284904734837684, 371284904736803509]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477256013975437, 362477302424837675⟩, ⟨427001480555202544, 428769718436653566⟩, true⟩

def words09 : List Nat := [371284904619114525, 371284904502095691, 371284904579318400, 371284904657373423, 371284904830444579, 371284905004222013, 371284905118923446, 371284905120823053, 371284904857223178, 371284904724809957]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk563B
