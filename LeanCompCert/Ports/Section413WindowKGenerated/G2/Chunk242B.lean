import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk242A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk242B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk242A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk242B
