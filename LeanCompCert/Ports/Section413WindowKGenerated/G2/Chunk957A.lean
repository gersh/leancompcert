import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk957A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588864780211495, 360588925268802669⟩, ⟨(-646379112344925671), (-642470257832092843)⟩, true⟩

def state01 : KState := ⟨⟨360598082625439192, 360598143127089819⟩, ⟨(-1528607422733642382), (-1524697318366202184)⟩, true⟩

def words00 : List Nat := [360582212141604241, 360582212235273203, 360582212249866915, 360582212264631549, 360582212265792628, 360582212307654024, 360582212472770382, 360582212638149593, 360582212738872971, 360582212906756042]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602193829117613, 360602254343879334⟩, ⟨(-1922170110750876449), (-1918258751456375855)⟩, true⟩

def words01 : List Nat := [360582213014481814, 360582213122585557, 360582213339462222, 360582213447742245, 360582213463182712, 360582213478717672, 360582213603162231, 360582213819041940, 360582214029535642, 360582214240334069]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360605407584085051, 360605468112056312⟩, ⟨(-2229847299694128989), (-2225934675916320505)⟩, true⟩

def words02 : List Nat := [360582214395991218, 360582214582523093, 360582214877937400, 360582215173767697, 360582215391568747, 360582215559284181, 360582215651371856, 360582215743607026, 360582215894073504, 360582216138548083]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585815359000798, 360585875900054161⟩, ⟨(-354122751952615717), (-350208875759708951)⟩, true⟩

def words03 : List Nat := [360582216491704329, 360582216845150419, 360582217114095817, 360582217297747173, 360582217431601326, 360582217565820493, 360582217808767869, 360582217943173141, 360582217982638827, 360582218022282259]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360611951637354040, 360612012191515183⟩, ⟨(-2856545814685766834), (-2852630683490607524)⟩, true⟩

def words04 : List Nat := [360582218109636967, 360582218251795440, 360582218470220556, 360582218688920435, 360582218813803545, 360582218943645400, 360582219182304842, 360582219421367476, 360582219702520181, 360582220015104591]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk957A
