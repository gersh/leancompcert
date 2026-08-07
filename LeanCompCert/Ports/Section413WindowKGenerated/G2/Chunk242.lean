import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk242

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

def state06 : KState := ⟨⟨360717923743159560, 360717927218286463⟩, ⟨(-3272697799940975803), (-3272640764738524589)⟩, true⟩

def words05 : List Nat := [360582994161139824, 360582998560055002, 360583004140982945, 360583008625179407, 360583011341483939, 360583014057579470, 360583017993295322, 360583023026897747, 360583028587920664, 360583034148555681]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360699901873254281, 360699905351394888⟩, ⟨(-2835567311981551920), (-2835510203651272310)⟩, true⟩

def words06 : List Nat := [360583038849018641, 360583043595005780, 360583049049761974, 360583054504163379, 360583059019303316, 360583063286979147, 360583066695459454, 360583070103693316, 360583073451419810, 360583078265421864]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606577333017848, 360606580814138070⟩, ⟨(-569993050589943267), (-569935869929814881)⟩, true⟩

def words07 : List Nat := [360583083556979116, 360583088848159796, 360583093041389014, 360583096197691530, 360583098903604701, 360583101609384869, 360583104551408612, 360583106375951799, 360583107343055751, 360583108310125476]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360685680400481412, 360685683884593695⟩, ⟨(-2491049975115445892), (-2490992721793506416)⟩, true⟩

def words08 : List Nat := [360583110973161396, 360583114756726492, 360583118480959216, 360583122204942638, 360583124504749679, 360583125121594752, 360583126909128838, 360583128696610752, 360583131693161640, 360583135915313159]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604069550836998, 360604073037966171⟩, ⟨(-508153185629875314), (-508095859012781326)⟩, true⟩

def words09 : List Nat := [360583139286979863, 360583142658400917, 360583146559143171, 360583151306163431, 360583155325387463, 360583159344332057, 360583161954080048, 360583162882233412, 360583163742991807, 360583164603785982]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk242
