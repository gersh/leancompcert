import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk944A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492946288554657, 362493081632291846⟩, ⟨(-755425158869361681), (-746798938540420827)⟩, true⟩

def state01 : KState := ⟨⟨362488757360786598, 362488892734398092⟩, ⟨(-359971813685526003), (-351342773064832811)⟩, true⟩

def words00 : List Nat := [371285170782149378, 371285170792119687, 371285170894862552, 371285170999282692, 371285171130412272, 371285171155160918, 371285171178743524, 371285171203472746, 371285171273402559, 371285171316628290]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480396698230681, 362480532101591790⟩, ⟨429424149480303123, 438055998915579003⟩, true⟩

def words01 : List Nat := [371285171440517635, 371285171565716283, 371285171669844826, 371285171673151736, 371285171627576875, 371285171596362810, 371285171630076686, 371285171633392763, 371285171587829025, 371285171542376747]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490498328822562, 362490633761812508⟩, ⟨(-524424943817348753), (-515790296680142623)⟩, true⟩

def words02 : List Nat := [371285171558585607, 371285171569418782, 371285171598511978, 371285171628969166, 371285171639866458, 371285171643176259, 371285171527060617, 371285171524894535, 371285171613910182, 371285171675244749]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490595495117865, 362490730958248228⟩, ⟨(-533591675841774541), (-524954182389786219)⟩, true⟩

def words03 : List Nat := [371285171735236785, 371285171796409662, 371285171968382999, 371285172085853553, 371285172178635276, 371285172272630560, 371285172343065768, 371285172346378403, 371285172354136311, 371285172417123190]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489230273507003, 362489365766107703⟩, ⟨(-404639292712169380), (-395999015928410570)⟩, true⟩

def words04 : List Nat := [371285172590422255, 371285172615329900, 371285172639083152, 371285172663986079, 371285172708358217, 371285172718056704, 371285172838474518, 371285172960280540, 371285173078550493, 371285173126369337]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk944A
