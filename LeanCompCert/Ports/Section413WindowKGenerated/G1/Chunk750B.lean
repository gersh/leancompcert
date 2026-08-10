import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk750A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk750B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk750A

def state06 : KState := ⟨⟨362477062954594751, 362477147023225208⟩, ⟨604139544318623137, 608400895775781461⟩, true⟩

def words05 : List Nat := [371285253098956161, 371285253037719673, 371285253002954358, 371285253005849955, 371285252970788301, 371285252951220073, 371285252930746186, 371285252911822646, 371285252655532408, 371285252550746868]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470757513653806, 362470841605307654⟩, ⟨1077465350919209455, 1081728430633991155⟩, true⟩

def words06 : List Nat := [371285252444543513, 371285252413264914, 371285252211720744, 371285252010245358, 371285251807743640, 371285251660367331, 371285251423243040, 371285251351239437, 371285251278361890, 371285251202092442]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489711712381358, 362489795827412891⟩, ⟨(-345539703222292257), (-341274868432654391)⟩, true⟩

def words07 : List Nat := [371285251011899058, 371285250958334404, 371285250984436559, 371285250987019910, 371285250833712377, 371285250632594614, 371285250430454235, 371285250395823223, 371285250341423054, 371285250404890114]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483775894638462, 362483860033009591⟩, ⟨100166155505544633, 104432742752301373⟩, true⟩

def words08 : List Nat := [371285250454835599, 371285250457466248, 371285250494804238, 371285250604269412, 371285250766567225, 371285250770660775, 371285250772612441, 371285250772426261, 371285250797711083, 371285250800658444]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468296476209872, 362468380637809097⟩, ⟨1262658321248405215, 1266926652812227521⟩, true⟩

def words09 : List Nat := [371285250916020866, 371285251050928723, 371285251185085985, 371285251187669986, 371285251085414720, 371285251008684980, 371285250942029729, 371285250944613835, 371285250721783119, 371285250500030299]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk750B
