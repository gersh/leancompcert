import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk231A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360655779139400865, 360655782276415395⟩, ⟨(-1738371792269674953), (-1738322765298676097)⟩, true⟩

def state01 : KState := ⟨⟨360592468826803140, 360592471966636903⟩, ⟨(-275715644113020875), (-275666552003054005)⟩, true⟩

def words00 : List Nat := [360580537267816249, 360580539208319431, 360580539794284491, 360580540380228946, 360580540485544937, 360580541529074733, 360580542503374037, 360580543477642117, 360580543513189424, 360580544029637074]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360690342009288904, 360690345151953656⟩, ⟨(-2538242392852677631), (-2538193235304589643)⟩, true⟩

def words01 : List Nat := [360580544683129252, 360580545336653961, 360580546955722132, 360580549467888335, 360580550172731957, 360580550877537651, 360580553449910789, 360580556958341734, 360580561707208882, 360580566455733571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360663003541164783, 360663006686693592⟩, ⟨(-1906379625524645790), (-1906330401745711964)⟩, true⟩

def words02 : List Nat := [360580569742434957, 360580572761093687, 360580576566705628, 360580580372075630, 360580583332752013, 360580585252231107, 360580585946334152, 360580586640413883, 360580588597211415, 360580592160657290]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592029054870920, 360592032203225259⟩, ⟨(-264184994814198452), (-264135705666369780)⟩, true⟩

def words03 : List Nat := [360580597588921243, 360580603016773093, 360580607020121459, 360580609958795788, 360580611632412539, 360580613305959453, 360580615578903408, 360580617028881460, 360580617522460879, 360580618016039469]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360680069275028178, 360680072426220836⟩, ⟨(-2301645248650897847), (-2301595893810469369)⟩, true⟩

def words04 : List Nat := [360580619828779715, 360580623222366263, 360580628478938574, 360580633735115896, 360580637395494158, 360580639917769923, 360580643780532670, 360580647643052255, 360580651436976186, 360580655731744984]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk231A
