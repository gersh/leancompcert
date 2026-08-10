import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk579A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk579B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk579A

def state06 : KState := ⟨⟨362478530386759799, 362478579507069073⟩, ⟨369212635025323313, 371135809895243975⟩, true⟩

def words05 : List Nat := [371284982386843119, 371284982515392491, 371284982698023993, 371284982769693692, 371284982907630322, 371284983046292571, 371284983182918036, 371284983184874220, 371284982924389760, 371284982816418543]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470417624680487, 362470466762404558⟩, ⟨839487227161022856, 841411411482951688⟩, true⟩

def words06 : List Nat := [371284982857282888, 371284982859239399, 371284982660728737, 371284982464604871, 371284982267756369, 371284982161262227, 371284981906080499, 371284981726077562, 371284981545413877, 371284981363258154]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507107323015971, 362507156478386996⟩, ⟨(-1287588209557488353), (-1285663002150010103)⟩, true⟩

def words07 : List Nat := [371284981114210128, 371284981085434014, 371284981322429985, 371284981376223013, 371284981380875089, 371284981386151139, 371284981688434033, 371284981842637304, 371284982226419022, 371284982611048558]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485166482556775, 362485215655605742⟩, ⟨(-15422974357350295), (-13496741893868287)⟩, true⟩

def words08 : List Nat := [371284982886824382, 371284982888782057, 371284982946230239, 371284983082171290, 371284983306678818, 371284983308636337, 371284983176718042, 371284983003786632, 371284982910798997, 371284982917044692]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476486542085729, 362476535732771168⟩, ⟨488048591164977377, 489975846455953805⟩, true⟩

def words09 : List Nat := [371284983220036717, 371284983523845668, 371284983823115319, 371284983825073129, 371284983765349046, 371284983723646050, 371284983876538671, 371284983878497124, 371284983735618479, 371284983592192823]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk579B
