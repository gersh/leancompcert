import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk469A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584826631071239, 360584840357856568⟩, ⟨(-91079163209018118), (-90644126541867706)⟩, true⟩

def state01 : KState := ⟨⟨360601178324576721, 360601192057439806⟩, ⟨(-858013611388275333), (-857578289643802535)⟩, true⟩

def words00 : List Nat := [360582908183601260, 360582908907070210, 360582909592384280, 360582910277798373, 360582910544611454, 360582910545255981, 360582910514006131, 360582910471971528, 360582910703337731, 360582911093707552]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590030817416997, 360590044556416237⟩, ⟨(-335032539295641162), (-334596929674149992)⟩, true⟩

def words01 : List Nat := [360582911201850583, 360582911310058288, 360582911706504731, 360582912449316826, 360582912889133296, 360582913329032988, 360582913481732931, 360582913482377449, 360582913333818413, 360582913486539761]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599932344857283, 360599946089935338⟩, ⟨(-799798430144381128), (-799362535275242920)⟩, true⟩

def words02 : List Nat := [360582913628207735, 360582913628852856, 360582913536951238, 360582913218644459, 360582912900246670, 360582912464314552, 360582912667816887, 360582912950793503, 360582913007327212, 360582913370937762]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360621988729066747, 360622002480222340⟩, ⟨(-1835003215005586630), (-1834567034886770422)⟩, true⟩

def words03 : List Nat := [360582914060543779, 360582914750309324, 360582915892568905, 360582916770796609, 360582917205405053, 360582917640029521, 360582917911929726, 360582918411736031, 360582919244896190, 360582920078166850]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576310719564368, 360576324476867835⟩, ⟨309285715327289499, 309722184057508237⟩, true⟩

def words04 : List Nat := [360582920685103521, 360582921310958230, 360582921857015746, 360582922403242436, 360582922718747570, 360582922719392437, 360582922582342672, 360582922219259350, 360582921856073805, 360582921328498453]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk469A
