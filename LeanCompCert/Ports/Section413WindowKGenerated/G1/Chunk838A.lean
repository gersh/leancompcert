import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk838A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476294281134890, 362476399960103271⟩, ⟨742270117861459867, 748249842273723315⟩, true⟩

def state01 : KState := ⟨⟨362481872555038937, 362481978260042933⟩, ⟨274828849978421004, 280810756303981622⟩, true⟩

def words00 : List Nat := [371285328865362634, 371285328868566725, 371285328890247041, 371285328970151334, 371285329012327317, 371285329015235059, 371285328867378244, 371285328838378406, 371285328820872144, 371285328823893357]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490113409637239, 362490219141119326⟩, ⟨(-415881630387006388), (-409897504797081380)⟩, true⟩

def words01 : List Nat := [371285328786137896, 371285328726536600, 371285328745364824, 371285328762458907, 371285328821942557, 371285328882565093, 371285328932966434, 371285328935925319, 371285328926300725, 371285328988236432]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480656247346308, 362480762004711432⟩, ⟨376883677287877836, 382869972528218048⟩, true⟩

def words02 : List Nat := [371285329179536507, 371285329182444963, 371285329184266859, 371285329187076027, 371285329196217421, 371285329199452733, 371285329163796062, 371285329192769021, 371285329220744656, 371285329223756264]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485271013217055, 362485376796935668⟩, ⟨(-9969655867626535), (-3981151283646435)⟩, true⟩

def words03 : List Nat := [371285329189920901, 371285329212148608, 371285329375013278, 371285329377922162, 371285329366168138, 371285329321339540, 371285329321915251, 371285329325121303, 371285329308518004, 371285329312396080]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490456761287977, 362490562571257743⟩, ⟨(-444798757818235611), (-438808052208853707)⟩, true⟩

def words04 : List Nat := [371285329315121706, 371285329318052334, 371285329252441189, 371285329293239345, 371285329353229735, 371285329356190671, 371285329317554144, 371285329274509215, 371285329317444021, 371285329383195480]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk838A
