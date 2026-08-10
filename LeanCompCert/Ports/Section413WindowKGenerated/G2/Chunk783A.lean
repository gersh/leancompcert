import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk783A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576185788837307, 360576225655094999⟩, ⟨470303853891756298, 472412124343742588⟩, true⟩

def state01 : KState := ⟨⟨360599416295363044, 360599456172161431⟩, ⟨(-1348724437484341472), (-1346615341644399186)⟩, true⟩

def words00 : List Nat := [360582259025246576, 360582259196400865, 360582259269124530, 360582259341967705, 360582259373902595, 360582259499357511, 360582259787347201, 360582260075543599, 360582260214654911, 360582260435398468]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360620763923972009, 360620803811330061⟩, ⟨(-3020572024787039045), (-3018462101968146559)⟩, true⟩

def words01 : List Nat := [360582260818737012, 360582261202399789, 360582261704106242, 360582262043360366, 360582262224505408, 360582262405750519, 360582262749584618, 360582263198397270, 360582263691395645, 360582264184640308]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584402798093361, 360584442696109670⟩, ⟨(-172694612472115051), (-170583854846323341)⟩, true⟩

def words02 : List Nat := [360582264596151380, 360582264845145096, 360582265052081410, 360582265259325023, 360582265374052798, 360582265375171282, 360582265327341128, 360582265195287911, 360582265063025409, 360582264965009004]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558533072263342, 360558572980812188⟩, ⟨1853825787706579258, 1855937370400400264⟩, true⟩

def words03 : List Nat := [360582265019235585, 360582265073668813, 360582265074665652, 360582265047580517, 360582264910164285, 360582264732416691, 360582264554348989, 360582264303256958, 360582264083324069, 360582263782068257]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597434094336278, 360597474013436330⟩, ⟨(-1193844316817581975), (-1191731907488510143)⟩, true⟩

def words04 : List Nat := [360582263480566626, 360582263342131650, 360582263443138315, 360582263559943079, 360582263560984759, 360582263540286304, 360582263456838939, 360582263497245166, 360582263649705171, 360582263844995743]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk783A
