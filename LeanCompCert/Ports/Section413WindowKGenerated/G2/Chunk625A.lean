import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk625A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554948828287387, 360554973778005842⟩, ⟨1732243071341575743, 1733296473351392859⟩, true⟩

def state01 : KState := ⟨⟨360587503217100596, 360587528175112257⟩, ⟨(-302570660462888377), (-301516740086906043)⟩, true⟩

def words00 : List Nat := [360582706078571913, 360582705900807389, 360582705903723236, 360582705906798840, 360582705907616023, 360582705695224768, 360582705227585069, 360582705016005748, 360582704804177820, 360582704756192597]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569093098721252, 360569118065082154⟩, ⟨848341227512619946, 849395669841293868⟩, true⟩

def words01 : List Nat := [360582704756974292, 360582704679388051, 360582704601641023, 360582704692117292, 360582704757038761, 360582704822101365, 360582704822900449, 360582704671326043, 360582704264593894, 360582704048284990]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576834318451843, 360576859293079237⟩, ⟨364275345921955851, 365330305111155599⟩, true⟩

def words02 : List Nat := [360582703831691840, 360582703807586301, 360582703624787215, 360582703314417254, 360582703003893041, 360582702551450936, 360582702279956163, 360582702161861648, 360582702043676766, 360582701773570380]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596349890613658, 360596374873533824⟩, ⟨(-856233368729666869), (-855177890951968235)⟩, true⟩

def words03 : List Nat := [360582701680859024, 360582701581597364, 360582701637376317, 360582701638254080, 360582701539492711, 360582701184688273, 360582700829728095, 360582700595267269, 360582700777790207, 360582700997341375]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577810909046385, 360577835900331462⟩, ⟨303087323467446856, 304143324427762000⟩, true⟩

def words04 : List Nat := [360582701089228678, 360582701090106595, 360582700927078798, 360582700717738247, 360582700508184642, 360582700124860849, 360582699702085081, 360582699150779274, 360582698599321075, 360582698303599692]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk625A
