import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495354317603752, 362495471019641582⟩, ⟨(-910472492459704642), (-903546242632509604)⟩, true⟩

def state01 : KState := ⟨⟨362485775951155804, 362485892680462463⟩, ⟨(-68496275071859965), (-61567628175197767)⟩, true⟩

def words00 : List Nat := [371285192050915797, 371285192053977298, 371285192047981513, 371285192043353949, 371285192069155047, 371285192073315840, 371285192158019460, 371285192243934545, 371285192328888268, 371285192340025258]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497990591281680, 362498107348346936⟩, ⟨(-1142346607480915450), (-1135415520191663700)⟩, true⟩

def words01 : List Nat := [371285192479352281, 371285192620357313, 371285192796381023, 371285192816454448, 371285192818823551, 371285192818390573, 371285192942281421, 371285193006565587, 371285193155539145, 371285193305965803]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480485069037616, 362480601853710575⟩, ⟨396790590925860246, 403724105627994192⟩, true⟩

def words02 : List Nat := [371285193455495962, 371285193458558037, 371285193476883062, 371285193521914240, 371285193603866782, 371285193606929004, 371285193516701625, 371285193407170034, 371285193296366604, 371285193279909006]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482383980747500, 362482500792968999⟩, ⟨229873221171052346, 236809158357383764⟩, true⟩

def words03 : List Nat := [371285193306779487, 371285193387107103, 371285193466443119, 371285193474290632, 371285193510360943, 371285193547991130, 371285193693188383, 371285193696251078, 371285193669375124, 371285193642165695]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482824600821765, 362482941440489534⟩, ⟨191130260555528606, 198068611507591398⟩, true⟩

def words04 : List Nat := [371285193613663366, 371285193608408036, 371285193593204477, 371285193652510651, 371285193672925615, 371285193675988705, 371285193523804669, 371285193482936776, 371285193496569922, 371285193499744879]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879A
