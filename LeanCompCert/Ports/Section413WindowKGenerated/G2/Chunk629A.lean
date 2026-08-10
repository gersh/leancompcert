import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk629A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360635911686929806, 360635936969845199⟩, ⟨(-3352188632895366094), (-3351114339388859210)⟩, true⟩

def state01 : KState := ⟨⟨360612976735779831, 360613002027126000⟩, ⟨(-1909458671045582905), (-1908383847202186349)⟩, true⟩

def words00 : List Nat := [360582661646604750, 360582662340690217, 360582663286973591, 360582664233486053, 360582665040810502, 360582665671942910, 360582666145023492, 360582666618181778, 360582666883091055, 360582667366300355]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584241171991675, 360584266471657430⟩, ⟨(-101492119610414589), (-100416772340728951)⟩, true⟩

def words01 : List Nat := [360582668023285618, 360582668680419068, 360582669184521156, 360582669502162017, 360582669755921302, 360582670009923877, 360582670349199863, 360582670500956202, 360582670527115858, 360582670553405325]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360623940547819323, 360623965855831509⟩, ⟨(-2599647520162087051), (-2598571647694262689)⟩, true⟩

def words02 : List Nat := [360582670831741161, 360582671236195768, 360582671573396068, 360582671910742379, 360582672031800091, 360582672032683989, 360582672165997053, 360582672359389813, 360582672804721410, 360582673461817522]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601158119202607, 360601183435626967⟩, ⟨(-1165862908116979438), (-1164786506229478678)⟩, true⟩

def words03 : List Nat := [360582673927617034, 360582674393492990, 360582674849428988, 360582675483149059, 360582675993104846, 360582676503188387, 360582676797362258, 360582676840119258, 360582677134869435, 360582677429903679]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612608058704104, 360612633383452070⟩, ⟨(-1886565809018715905), (-1885488883201070871)⟩, true⟩

def words04 : List Nat := [360582677925208581, 360582678381311482, 360582678710384859, 360582679039559730, 360582679304898972, 360582679732869862, 360582680269469660, 360582680806220260, 360582681216003682, 360582681692721168]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk629A
