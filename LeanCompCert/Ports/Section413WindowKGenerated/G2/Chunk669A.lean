import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk669A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589112490076125, 360589141232220190⟩, ⟨(-417582039465352565), (-416283165612820143)⟩, true⟩

def state01 : KState := ⟨⟨360601335994569143, 360601364745599200⟩, ⟨(-1235390226971988273), (-1234090758602515925)⟩, true⟩

def words00 : List Nat := [360582919125216693, 360582919360591286, 360582919457662142, 360582919554832374, 360582919595863655, 360582919821406125, 360582920152684835, 360582920484133746, 360582920703991257, 360582920980618816]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604400665536594, 360604429425489891⟩, ⟨(-1440586897521533459), (-1439286832053801647)⟩, true⟩

def words01 : List Nat := [360582921323086232, 360582921665820031, 360582921879053563, 360582921879997693, 360582921870456477, 360582921670675689, 360582921470720232, 360582921528634401, 360582921850794870, 360582922173176659]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583942441130940, 360583971210075918⟩, ⟨(-71501756641966359), (-70201089407587295)⟩, true⟩

def words02 : List Nat := [360582922383994639, 360582922384938845, 360582922582762228, 360582922793742390, 360582922946128397, 360582922947072681, 360582922927607524, 360582922734773050, 360582922541765836, 360582922352455271]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360552993548721516, 360553022326555749⟩, ⟨2000183813970413509, 2001485076207530719⟩, true⟩

def words03 : List Nat := [360582922591641235, 360582922831001801, 360582922907995714, 360582922992743389, 360582922993539045, 360582922931699789, 360582922869590605, 360582922776042264, 360582922459673439, 360582922013980421]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603332072411315, 360603360859176035⟩, ⟨(-1369831558845026845), (-1368529698756999353)⟩, true⟩

def words04 : List Nat := [360582921568100180, 360582921069787228, 360582920683520010, 360582920520145632, 360582920356702664, 360582920003166222, 360582919726617057, 360582919673055994, 360582919787262519, 360582920093560033]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk669A
