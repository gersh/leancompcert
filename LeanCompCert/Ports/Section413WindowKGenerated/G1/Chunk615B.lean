import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk615A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk615B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk615A

def state06 : KState := ⟨⟨362490244440792852, 362490300117996102⟩, ⟨(-307274609122812378), (-304959465724728486)⟩, true⟩

def words05 : List Nat := [371285346202934681, 371285346096676459, 371285346145154506, 371285346171493889, 371285346245791694, 371285346320875415, 371285346357536046, 371285346359659817, 371285346257891591, 371285346340998901]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475584676437980, 362475640372217110⟩, ⟨595290134321663218, 597606421347563268⟩, true⟩

def words06 : List Nat := [371285346686999534, 371285346689087013, 371285346683504612, 371285346677786224, 371285346678694659, 371285346680996754, 371285346572230205, 371285346548928421, 371285346524895478, 371285346502172406]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495346470977439, 362495402185631544⟩, ⟨(-621518568561772761), (-619201119307326031)⟩, true⟩

def words07 : List Nat := [371285346374920390, 371285346406408546, 371285346658688958, 371285346660782734, 371285346643503269, 371285346580637902, 371285346697178015, 371285346787663592, 371285346952397978, 371285347118008295]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490327591273196, 362490383324754323⟩, ⟨(-312457019754934056), (-310138411034699206)⟩, true⟩

def words08 : List Nat := [371285347280901364, 371285347282990585, 371285347260105192, 371285347382443325, 371285347584767494, 371285347604272293, 371285347621422606, 371285347639242491, 371285347790450910, 371285347874590587]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484578664732908, 362484634417090625⟩, ⟨41692488899436105, 44012260318692195⟩, true⟩

def words09 : List Nat := [371285348124129009, 371285348374523452, 371285348568085973, 371285348570187916, 371285348610982930, 371285348656177694, 371285348918120137, 371285348920213647, 371285348910998137, 371285348901836059]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk615B
