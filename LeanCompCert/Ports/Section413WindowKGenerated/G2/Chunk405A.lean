import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk405A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360550841478536326, 360550851592070086⟩, ⟨1283718223943705408, 1283995055511410880⟩, true⟩

def state01 : KState := ⟨⟨360587384977116032, 360587395095830037⟩, ⟨(-196416107441008022), (-196139066047554118)⟩, true⟩

def words00 : List Nat := [360582554391346744, 360582554053213817, 360582554051029650, 360582553648051909, 360582553245004408, 360582552687000860, 360582552949241656, 360582553384671171, 360582553385173658, 360582553470936859]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602905409251697, 360602915533148906⟩, ⟨(-825386712046231155), (-825109460654972379)⟩, true⟩

def words01 : List Nat := [360582553795914294, 360582554121035376, 360582554300332257, 360582554300881916, 360582554089593076, 360582553310246446, 360582552530824081, 360582552117350734, 360582552515288517, 360582553018387302]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576270209846216, 360576280338986852⟩, ⟨253695560165189970, 253973024045243966⟩, true⟩

def words02 : List Nat := [360582553138266378, 360582553138816046, 360582552652303021, 360582552137267284, 360582551622108150, 360582550954192196, 360582550014014558, 360582548685547040, 360582547357038494, 360582546636150564]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360522748844201387, 360522758978514149⟩, ⟨2423368052104256871, 2423645725637394505⟩, true⟩

def words03 : List Nat := [360582546934725029, 360582547387987379, 360582547452146361, 360582547452698744, 360582547341619727, 360582546793352396, 360582546244953270, 360582545680897690, 360582544511027741, 360582543036867317]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576710593348868, 360576720732853199⟩, ⟨235605460532325672, 235883344556496414⟩, true⟩

def words04 : List Nat := [360582541562655319, 360582540509983884, 360582539843315667, 360582539783741704, 360582539724124466, 360582539076524909, 360582538646742996, 360582538393877785, 360582538140864526, 360582537831362608]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk405A
