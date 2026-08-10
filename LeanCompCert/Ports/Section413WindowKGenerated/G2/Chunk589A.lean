import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk589A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360540262928510503, 360540284982751693⟩, ⟨2458881633899792371, 2459759224998259815⟩, true⟩

def state01 : KState := ⟨⟨360569483066498917, 360569505128503371⟩, ⟨737631814722433019, 738509863115319353⟩, true⟩

def words00 : List Nat := [360582045891126391, 360582045471281535, 360582045194900250, 360582044879051746, 360582044563176990, 360582043923496639, 360582042996256103, 360582042357486484, 360582041718497076, 360582041367904412]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360553070921855582, 360553092991707041⟩, ⟨1704637015640364812, 1705515526339237250⟩, true⟩

def words01 : List Nat := [360582041155837972, 360582040783419256, 360582040410841188, 360582040385975527, 360582040386664199, 360582040372747898, 360582040358733010, 360582040168302071, 360582039774086782, 360582039283735881]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564656823449053, 360564678901051469⟩, ⟨1021958428757847843, 1022837396181549511⟩, true⟩

def words02 : List Nat := [360582038793128382, 360582038590802147, 360582038291794699, 360582037848469271, 360582037405025312, 360582036888490017, 360582036614024501, 360582036376986703, 360582036139869767, 360582035720942553]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584712605020568, 360584734690403477⟩, ⟨(-160100870782401333), (-159221444816207177)⟩, true⟩

def words03 : List Nat := [360582035427080709, 360582035306414898, 360582035185514715, 360582035056216277, 360582034721738128, 360582034144103651, 360582033566330748, 360582033276780367, 360582033273777712, 360582033320477344]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560810137680378, 360560832230907707⟩, ⟨1248785188728146141, 1249665077082376563⟩, true⟩

def words04 : List Nat := [360582033321218843, 360582033159751975, 360582032958211725, 360582033001966244, 360582033002655221, 360582032972321415, 360582032654925738, 360582032113348392, 360582031571637030, 360582030959950666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk589A
