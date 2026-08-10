import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk871A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480473585299576, 362480588091831809⟩, ⟨394309232806551819, 401043374262422457⟩, true⟩

def state01 : KState := ⟨⟨362484534792165282, 362484649325871099⟩, ⟨40570205566606031, 47306713977760561⟩, true⟩

def words00 : List Nat := [371285192442605360, 371285192425676927, 371285192388513322, 371285192438068534, 371285192465276770, 371285192468308641, 371285192333522102, 371285192332009206, 371285192391424263, 371285192394565598]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484301266206913, 362484415827580087⟩, ⟨60916127888390011, 67655046537863081⟩, true⟩

def words01 : List Nat := [371285192390618891, 371285192387785904, 371285192465126317, 371285192484033531, 371285192504488177, 371285192526037763, 371285192541158889, 371285192544192426, 371285192405710733, 371285192400657887]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482833804983425, 362482948393375237⟩, ⟨188814323484954520, 195555596139590870⟩, true⟩

def words02 : List Nat := [371285192516504822, 371285192539485529, 371285192562217725, 371285192585951077, 371285192603057499, 371285192606415431, 371285192656159808, 371285192741399598, 371285192801989782, 371285192805129393]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498023017919890, 362498137633694836⟩, ⟨(-1134706010084559019), (-1127962351398395477)⟩, true⟩

def words03 : List Nat := [371285192814298957, 371285192850753672, 371285193017250669, 371285193048323972, 371285193050672078, 371285193048932398, 371285193160686291, 371285193225038051, 371285193375651915, 371285193527574888]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488453480090270, 362488568123250882⟩, ⟨(-300804770052358335), (-294058724839271007)⟩, true⟩

def words04 : List Nat := [371285193677797845, 371285193740587400, 371285193840593999, 371285193942162287, 371285194064500739, 371285194067534144, 371285194014577829, 371285193951333289, 371285193951913217, 371285193994154954]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk871A
