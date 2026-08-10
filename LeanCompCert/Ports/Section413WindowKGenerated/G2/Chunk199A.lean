import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk199A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360420561384135988, 360420563681726048⟩, ⟨3221147491126581661, 3221178434199578979⟩, true⟩

def state01 : KState := ⟨⟨360474268083728810, 360474270383729463⟩, ⟨2151929755004080802, 2151960746059683386⟩, true⟩

def words00 : List Nat := [360582423811286123, 360582415617184527, 360582408857078757, 360582402815098415, 360582396773705118, 360582388593508968, 360582379146296692, 360582370512074045, 360582361878637170, 360582354800909759]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360492596275596658, 360492598578023451⟩, ⟨1786863261829402095, 1786894301201820705⟩, true⟩

def words01 : List Nat := [360582349372759863, 360582342680539352, 360582335988941743, 360582331807559387, 360582328920456986, 360582324245963801, 360582319571912977, 360582313622632303, 360582306610324911, 360582302107200250]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360510201570767409, 360510203875602020⟩, ⟨1436014486124987630, 1436045573473118906⟩, true⟩

def words02 : List Nat := [360582297604444977, 360582293474236722, 360582289479799677, 360582283848039090, 360582278216801772, 360582271902527616, 360582267143788045, 360582264892159622, 360582262640734069, 360582258344918283]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578648270326836, 360578650577570551⟩, ⟨71306047848567298, 71337183222456394⟩, true⟩

def words03 : List Nat := [360582254729929522, 360582252190519326, 360582249651287806, 360582248576701780, 360582244989549695, 360582239254540205, 360582233520052934, 360582230289903222, 360582228348669974, 360582228169507485]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360502711985905162, 360502714295586447⟩, ⟨1585305395599160689, 1585336579589703603⟩, true⟩

def words04 : List Nat := [360582227990327149, 360582225805155410, 360582223425331815, 360582219356470787, 360582215287947898, 360582210579437708, 360582203361611987, 360582194669420150, 360582185978050982, 360582179788297711]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk199A
