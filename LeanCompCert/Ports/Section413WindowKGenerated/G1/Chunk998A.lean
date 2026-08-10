import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk998A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487917762665841, 362488069681722362⟩, ⟨(-280727108507500885), (-270490980611049815)⟩, true⟩

def state01 : KState := ⟨⟨362479453367598394, 362479605318332714⟩, ⟨564011985611422852, 574251275117454336⟩, true⟩

def words00 : List Nat := [371285359406377561, 371285359409886875, 371285359312851236, 371285359253855831, 371285359193162844, 371285359163868377, 371285359050286449, 371285358921354245, 371285358790945650, 371285358762628050]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481903161637766, 362482055143975667⟩, ⟨319520057551399929, 329762501570940087⟩, true⟩

def words01 : List Nat := [371285358741593596, 371285358779599303, 371285358788195949, 371285358791746523, 371285358739026401, 371285358718371011, 371285358771383815, 371285358774896729, 371285358744527785, 371285358715419977]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492090552183370, 362492242565926925⟩, ⟨(-697405711285708757), (-687160132198170951)⟩, true⟩

def words02 : List Nat := [371285358742304901, 371285358758755227, 371285358874111722, 371285358990952458, 371285359076379565, 371285359079899799, 371285359104501011, 371285359132647775, 371285359259354985, 371285359331939505]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496507979199147, 362496660024959247⟩, ⟨(-1138407122745451231), (-1128158347289326811)⟩, true⟩

def words03 : List Nat := [371285359401610303, 371285359472497472, 371285359642302201, 371285359777172080, 371285359926178626, 371285360076520880, 371285360225720150, 371285360242040614, 371285360357599761, 371285360475202241]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478594461320006, 362478746538378362⟩, ⟨650160508183124860, 660412408619509532⟩, true⟩

def words04 : List Nat := [371285360608099826, 371285360611610711, 371285360610974487, 371285360603079104, 371285360606122812, 371285360610033831, 371285360578782099, 371285360581242175, 371285360582417436, 371285360583532288]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk998A
