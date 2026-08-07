import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk858

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

def state06 : KState := ⟨⟨360587675748500493, 360587724029370381⟩, ⟨(-466620460959946863), (-463820995082408637)⟩, true⟩

def words05 : List Nat := [360582320665693865, 360582320777536745, 360582321024671987, 360582321359325993, 360582321562967233, 360582321766780054, 360582321902473660, 360582321903707973, 360582321966509065, 360582322030848557]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588668537144993, 360588716829656962⟩, ⟨(-551858755950784259), (-549058290425988299)⟩, true⟩

def words06 : List Nat := [360582322154610606, 360582322282358035, 360582322341989986, 360582322401755328, 360582322402793229, 360582322476119001, 360582322610479994, 360582322745071840, 360582322764206266, 360582322839946513]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597444691267141, 360597492995430289⟩, ⟨(-1305531636063333225), (-1302730169994454733)⟩, true⟩

def words07 : List Nat := [360582323001286089, 360582323162984262, 360582323426505973, 360582323554591760, 360582323563009061, 360582323571542344, 360582323572547542, 360582323624970691, 360582323802603086, 360582323980514366]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586588040200415, 360586636356133415⟩, ⟨(-373227538699917541), (-370425061777655829)⟩, true⟩

def words08 : List Nat := [360582324090321567, 360582324138275144, 360582324182532836, 360582324227138519, 360582324228171798, 360582324219692580, 360582324075461403, 360582323862393221, 360582323649084694, 360582323621833225]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554362270294022, 360554410597848936⟩, ⟨2394855807883527736, 2397659283070963536⟩, true⟩

def words09 : List Nat := [360582323713490917, 360582323805378576, 360582323829238731, 360582323830473747, 360582323760293348, 360582323624164902, 360582323487681817, 360582323347887874, 360582323136680818, 360582322813018564]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk858
