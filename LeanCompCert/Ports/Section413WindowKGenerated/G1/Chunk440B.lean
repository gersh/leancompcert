import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk440A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk440B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk440A

def state06 : KState := ⟨⟨362508924799080077, 362508952562974533⟩, ⟨(-1031784186228224419), (-1030957663038400883)⟩, true⟩

def words05 : List Nat := [371285552171838067, 371285552374904221, 371285553092554078, 371285553123961631, 371285553125106731, 371285552993142181, 371285553063412174, 371285553080961307, 371285553613031759, 371285554145711230]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492985617396742, 362493013394435719⟩, ⟨(-329511903107809655), (-328684800706269577)⟩, true⟩

def words06 : List Nat := [371285554662025412, 371285554663481714, 371285554792512007, 371285555093566591, 371285555417318699, 371285555418784905, 371285555282261183, 371285555090665292, 371285555149047773, 371285555319948953]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463172183714518, 362463199973892822⟩, ⟨984657568450286520, 985485249969174336⟩, true⟩

def words07 : List Nat := [371285556005082869, 371285556690817726, 371285557342691312, 371285557344148200, 371285557326070101, 371285557344022075, 371285557625625164, 371285557627082151, 371285557222849879, 371285556717313176]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495668962370382, 362495696765587889⟩, ⟨(-447954394573438362), (-447126138220003876)⟩, true⟩

def words08 : List Nat := [371285556211130585, 371285556027578786, 371285555632043401, 371285555573272411, 371285555514064184, 371285555377532783, 371285554948288731, 371285554992193520, 371285555549785468, 371285555781300393]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482117486624125, 362482145303145924⟩, ⟨149635278384425209, 150464121387536429⟩, true⟩

def words09 : List Nat := [371285555954190740, 371285556127538819, 371285556514057817, 371285556645077881, 371285556930472814, 371285557216440726, 371285557500850582, 371285557502312166, 371285557263515234, 371285557187984644]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk440B
