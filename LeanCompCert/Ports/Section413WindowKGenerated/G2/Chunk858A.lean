import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk858A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572869912468406, 360572918123294608⟩, ⟨804427289761739439, 807220743790161707⟩, true⟩

def state01 : KState := ⟨⟨360574174160183841, 360574222382612267⟩, ⟨692485979082740162, 695280428639839450⟩, true⟩

def words00 : List Nat := [360582326183288903, 360582326184522265, 360582326051201844, 360582325830613986, 360582325609827343, 360582325344420810, 360582325188555872, 360582325128348199, 360582325068006315, 360582324939757587]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572772557986538, 360572820792072353⟩, ⟨812638687556759825, 815434137493153627⟩, true⟩

def words01 : List Nat := [360582324846338946, 360582324723552453, 360582324600430689, 360582324372158732, 360582324038677175, 360582323589395546, 360582323139884532, 360582322826392388, 360582322581023316, 360582322471605017]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578513721857324, 360578561967687410⟩, ⟨319823144804099839, 322619602692467741⟩, true⟩

def words02 : List Nat := [360582322361988905, 360582322184461972, 360582322027507155, 360582321930769374, 360582321833695019, 360582321701327547, 360582321530266166, 360582321237870831, 360582320945245287, 360582320788643865]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571586182051541, 360571634439499567⟩, ⟨914509751005233610, 917307206118914028⟩, true⟩

def words03 : List Nat := [360582320837659388, 360582320930702642, 360582320931823723, 360582320902973550, 360582320877670425, 360582320818523237, 360582320834092165, 360582320835326121, 360582320806958476, 360582320683746060]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597579635886277, 360597627904999497⟩, ⟨(-1316949848991356780), (-1314151392481532014)⟩, true⟩

def words04 : List Nat := [360582320560272100, 360582320433634702, 360582320485142201, 360582320579420332, 360582320580558740, 360582320541589025, 360582320366649860, 360582320327654936, 360582320374392611, 360582320553978758]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk858A
