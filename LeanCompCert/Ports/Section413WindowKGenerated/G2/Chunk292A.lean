import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk292A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554017225292726, 360554022341568399⟩, ⟨850016473669017110, 850117511424779542⟩, true⟩

def state01 : KState := ⟨⟨360647536652744912, 360647541772665448⟩, ⟨(-1881320438039676643), (-1881219293835985331)⟩, true⟩

def words00 : List Nat := [360583135131141713, 360583136001978625, 360583136780536126, 360583137559119858, 360583137559481678, 360583137110638318, 360583136640627162, 360583136990632131, 360583138509894843, 360583140715055781]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360661290482696130, 360661295606301202⟩, ⟨(-2283245646339212316), (-2283144394491793732)⟩, true⟩

def words01 : List Nat := [360583141974023402, 360583143232939565, 360583145325917027, 360583148038853562, 360583150455350015, 360583152871746624, 360583154703256970, 360583156572915388, 360583159247390851, 360583161921810877]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360656221444867783, 360656226572111668⟩, ⟨(-2135109243663061766), (-2135007885470977530)⟩, true⟩

def words02 : List Nat := [360583165764101537, 360583169116320651, 360583171640708747, 360583174164963952, 360583175857206323, 360583178140857581, 360583180590653711, 360583183040354038, 360583184906111940, 360583187405286347]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360668658059642094, 360668663190543039⟩, ⟨(-2498675690304890174), (-2498574225198985936)⟩, true⟩

def words03 : List Nat := [360583191071531131, 360583194737649717, 360583198280835387, 360583201091206852, 360583202896357063, 360583204701414060, 360583206761006224, 360583209712440387, 360583212635244237, 360583215557931330]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360657711037114140, 360657716171701266⟩, ⟨(-2178779040794403580), (-2178677467886472592)⟩, true⟩

def words04 : List Nat := [360583217775691643, 360583218831141944, 360583221052949687, 360583223274718573, 360583225201107066, 360583227164439943, 360583228544543487, 360583229924594889, 360583231471497066, 360583234018342869]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk292A
