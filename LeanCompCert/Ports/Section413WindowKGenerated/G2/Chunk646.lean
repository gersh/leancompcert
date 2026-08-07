import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk646

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360573658087792721, 360573684812763955⟩, ⟨598287019942934006, 599453250317211438⟩, true⟩

def state01 : KState := ⟨⟨360595480010658873, 360595506744225341⟩, ⟨(-811561376256609215), (-810394590588759835)⟩, true⟩

def words00 : List Nat := [360582964227524517, 360582964497745336, 360582964641288867, 360582964784984902, 360582964785823841, 360582964711272798, 360582964397915154, 360582964144959359, 360582963891744736, 360582964072070619]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587782210747311, 360587808952978871⟩, ⟨(-314105215137101521), (-312937869575437353)⟩, true⟩

def words01 : List Nat := [360582964147072221, 360582964222163231, 360582964536231493, 360582965037138873, 360582965477601784, 360582965918199804, 360582966146380678, 360582966147290339, 360582966211765149, 360582966287752777]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592935396628743, 360592962147422442⟩, ⟨(-647162609570084263), (-645994710679948753)⟩, true⟩

def words02 : List Nat := [360582966602518575, 360582966744835871, 360582966745650227, 360582966737999529, 360582966730191227, 360582966549041013, 360582966663675999, 360582966841061080, 360582966870126677, 360582967025721093]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360623446458281080, 360623473217680229⟩, ⟨(-2619319595686572777), (-2618151140585685039)⟩, true⟩

def words03 : List Nat := [360582967173271288, 360582967321070706, 360582967707621906, 360582968014632676, 360582968121908527, 360582968229261781, 360582968525587218, 360582969013576664, 360582969640924831, 360582970268459368]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590933668078256, 360590960436134746⟩, ⟨(-517636570169080653), (-516467555413558837)⟩, true⟩

def words04 : List Nat := [360582970749415423, 360582970992092953, 360582971423538581, 360582971855237708, 360582972121761503, 360582972150064699, 360582972150888605, 360582971998899501, 360582971846744432, 360582971889083447]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk646
