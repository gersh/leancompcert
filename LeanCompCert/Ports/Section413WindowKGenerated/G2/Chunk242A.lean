import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk242A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360707399938134358, 360707403395332295⟩, ⟨(-3014263669292265584), (-3014207068507605958)⟩, true⟩

def state01 : KState := ⟨⟨360732124163215506, 360732127623417884⟩, ⟨(-3613096524965275120), (-3613039851458383686)⟩, true⟩

def words00 : List Nat := [360582858817970938, 360582861411077282, 360582865711391918, 360582870011443222, 360582873529198019, 360582878070907376, 360582881749328251, 360582885427480429, 360582890124027686, 360582896288427245]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586665167725225, 360586668630903435⟩, ⟨(-90758231585241058), (-90701486018463504)⟩, true⟩

def words01 : List Nat := [360582902075669716, 360582907862492413, 360582912346031382, 360582915136968110, 360582917104111956, 360582919071176307, 360582922169341981, 360582923575327804, 360582923730240229, 360582923885186146]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360658393714920456, 360658397181076908⟩, ⟨(-1828267617350567826), (-1828210799635783826)⟩, true⟩

def words02 : List Nat := [360582925163534284, 360582927767186480, 360582932075257758, 360582936383033540, 360582939119532089, 360582940164486547, 360582941147052149, 360582942129627470, 360582944815928282, 360582947930132425]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360629644216102442, 360629647685264865⟩, ⟨(-1131580962685061307), (-1131524072120534625)⟩, true⟩

def words03 : List Nat := [360582950006470548, 360582952082673015, 360582954394179220, 360582958047665946, 360582960816898802, 360582963585954438, 360582965499412783, 360582965722847253, 360582967648926472, 360582969574950913]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360648409151683663, 360648412623827819⟩, ⟨(-1586626786152508406), (-1586569823296215730)⟩, true⟩

def words04 : List Nat := [360582971439202730, 360582973799667991, 360582975298932473, 360582976798110686, 360582977348393398, 360582978769668294, 360582981892351032, 360582985014841851, 360582987063776861, 360582989761954238]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk242A
