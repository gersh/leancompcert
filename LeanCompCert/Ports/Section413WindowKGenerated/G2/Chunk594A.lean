import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk594A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584536916878965, 360584559362224443⟩, ⟨(-150970974602319062), (-150070249553100398)⟩, true⟩

def state01 : KState := ⟨⟨360604388142102577, 360604410595270790⟩, ⟨(-1330224695769258147), (-1329323506010139199)⟩, true⟩

def words00 : List Nat := [360582033237354313, 360582033511718059, 360582033643288302, 360582033774944974, 360582033823497036, 360582034012977129, 360582034485688244, 360582034958543046, 360582035177709441, 360582035555193866]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360620822814087457, 360620845275089536⟩, ⟨(-2306820984153079419), (-2305919328944133347)⟩, true⟩

def words01 : List Nat := [360582035969386080, 360582036383803613, 360582036797628164, 360582037016684091, 360582037017451881, 360582036959319551, 360582037125440467, 360582037496097524, 360582038149878627, 360582038803826109]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610169711189561, 360610192180112508⟩, ⟨(-1673895381809670756), (-1672993255905097294)⟩, true⟩

def words02 : List Nat := [360582039286652949, 360582039841567246, 360582040281095226, 360582040720837399, 360582041087954003, 360582041277780538, 360582041294161437, 360582041310624502, 360582041527021694, 360582042001655052]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566978446695205, 360567000923440224⟩, ⟨893259248796490869, 894161839605886997⟩, true⟩

def words03 : List Nat := [360582042687784355, 360582043374055104, 360582043847486032, 360582044038943920, 360582044157720484, 360582044276726368, 360582044384231287, 360582044385062307, 360582044275254376, 360582044023029826]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601585794262760, 360601608278848497⟩, ⟨(-1163903472202349754), (-1163000415301642238)⟩, true⟩

def words04 : List Nat := [360582043800733615, 360582043972235652, 360582044426654382, 360582044881237338, 360582045094967611, 360582045095798644, 360582045241679898, 360582045456763217, 360582045613304924, 360582045943222492]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk594A
