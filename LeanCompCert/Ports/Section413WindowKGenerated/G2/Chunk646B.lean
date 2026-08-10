import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk646A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk646B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk646A

def state06 : KState := ⟨⟨360550368200274197, 360550394976913022⟩, ⟨2105163652541010902, 2106333222187728230⟩, true⟩

def words05 : List Nat := [360582972094833046, 360582972300764346, 360582972352625205, 360582972353535357, 360582972167041159, 360582971884605754, 360582971601904894, 360582971320188855, 360582971001306216, 360582970498443918]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608597168079549, 360608623953310018⟩, ⟨(-1660175595285618859), (-1659005470060911221)⟩, true⟩

def words06 : List Nat := [360582969995390678, 360582969731441850, 360582969747705786, 360582969875782932, 360582969876631066, 360582969802810326, 360582970038263374, 360582970276014125, 360582970550943333, 360582970948561972]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596286053911681, 360596312847828227⟩, ⟨(-863991477551332758), (-862820790556328948)⟩, true⟩

def words07 : List Nat := [360582971226082193, 360582971503693768, 360582971775152994, 360582972167232106, 360582972428815263, 360582972690537993, 360582972832244794, 360582972833155387, 360582973007702158, 360582973215006281]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578459119622825, 360578485922100998⟩, ⟨289130181390966168, 290301422196615790⟩, true⟩

def words08 : List Nat := [360582973592293024, 360582973731624006, 360582973751076312, 360582973770619834, 360582973771383992, 360582973649243887, 360582973646267227, 360582973637528766, 360582973628686991, 360582973500122279]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360601368320634737, 360601395131706225⟩, ⟨(-1192983914499775564), (-1191812117749743640)⟩, true⟩

def words09 : List Nat := [360582973431494133, 360582973400668355, 360582973576294797, 360582973790258526, 360582973796566065, 360582973802942512, 360582973952826516, 360582974256165943, 360582974541616291, 360582974827263485]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk646B
