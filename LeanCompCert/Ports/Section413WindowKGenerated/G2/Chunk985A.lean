import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk985A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575206640486321, 360575270863415949⟩, ⟨700260588034118400, 704532073714760008⟩, true⟩

def state01 : KState := ⟨⟨360589129887020989, 360589194123449520⟩, ⟨(-671248614031870935), (-666975798640559035)⟩, true⟩

def words00 : List Nat := [360582423401849103, 360582423371049371, 360582423464442444, 360582423558132929, 360582423559474241, 360582423554819654, 360582423447152494, 360582423442896530, 360582423481437591, 360582423551649005]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588799257943676, 360588863508027113⟩, ⟨(-638739946269720478), (-634465785667378038)⟩, true⟩

def words01 : List Nat := [360582423552946250, 360582423543724235, 360582423534267930, 360582423602048756, 360582423603252641, 360582423588781593, 360582423574144910, 360582423508062213, 360582423536990255, 360582423603989727]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573083142774529, 360573147406324567⟩, ⟨909677039558529749, 913952526958924951⟩, true⟩

def words02 : List Nat := [360582423750731209, 360582423795034791, 360582423796323819, 360582423773024983, 360582423749515473, 360582423653132308, 360582423607697018, 360582423518048160, 360582423428244898, 360582423287040684]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592062845913390, 360592127123004241⟩, ⟨(-960488932486869775), (-956212110846738527)⟩, true⟩

def words03 : List Nat := [360582423194056631, 360582423161060978, 360582423195906144, 360582423221014354, 360582423222334590, 360582423160025120, 360582423121352252, 360582423225322647, 360582423324977122, 360582423424941032]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587595425033277, 360587659715762993⟩, ⟨(-520278305021181360), (-516000139341354152)⟩, true⟩

def words04 : List Nat := [360582423473163681, 360582423474596580, 360582423560407574, 360582423655766095, 360582423724650747, 360582423795902335, 360582423810222495, 360582423824698840, 360582423825868097, 360582423846625782]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk985A
