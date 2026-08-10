import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk218A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586361793817030, 360586364573381337⟩, ⟨(-139110488948777839), (-139069489144890513)⟩, true⟩

def state01 : KState := ⟨⟨360566299702247353, 360566302484489722⟩, ⟨298050402231671010, 298091460430630812⟩, true⟩

def words00 : List Nat := [360579985531885481, 360579984408982124, 360579983705156944, 360579984401697980, 360579984401937759, 360579983535056171, 360579980575661023, 360579976566725312, 360579972558103260, 360579970135128449]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360487785814641256, 360487788599539780⟩, ⟨2010995141573957829, 2011036257717099323⟩, true⟩

def words01 : List Nat := [360579969562273418, 360579969616112351, 360579969616364815, 360579968098378714, 360579966011752014, 360579963393883937, 360579960776170690, 360579960252367924, 360579957638054746, 360579953414283919]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598559287393699, 360598562074951367⟩, ⟨(-406566796264640494), (-406525622085972738)⟩, true⟩

def words02 : List Nat := [360579949190836800, 360579947061026844, 360579946419375939, 360579946854509177, 360579946854771479, 360579945356125797, 360579943927985280, 360579942030770205, 360579940133646093, 360579940590727742]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360549863879145378, 360549866669391200⟩, ⟨656566403299171103, 656607636173615115⟩, true⟩

def words03 : List Nat := [360579940590979327, 360579940148550010, 360579939706111347, 360579939764867501, 360579939765105096, 360579938943644453, 360579938122228396, 360579935964593845, 360579932497909446, 360579931121596952]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558545126135161, 360558547919035627⟩, ⟨466880879586032565, 466922170451263529⟩, true⟩

def words04 : List Nat := [360579930458686249, 360579930458968376, 360579929917215254, 360579928286861308, 360579926656611248, 360579923738902634, 360579922455057167, 360579921105870789, 360579919756777076, 360579917354754221]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk218A
