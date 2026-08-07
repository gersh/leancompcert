import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk035

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360445794110695681, 360445794170262190⟩, ⟨392210371205122168, 392210512843222678⟩, true⟩

def state01 : KState := ⟨⟨360009085371623326, 360009085431553797⟩, ⟨1922102317614069034, 1922102460527826288⟩, true⟩

def words00 : List Nat := [360557822308783568, 360557748668671147, 360557659666652445, 360557611872293232, 360557564105196252, 360557494798446101, 360557345508023536, 360557131937638351, 360556918488973413, 360556692970165714]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨359763850347969195, 359763850408260393⟩, ⟨2786146235220490823, 2786146379402266223⟩, true⟩

def words01 : List Nat := [360556537001088665, 360556460821430823, 360556384685139010, 360556267499032980, 360556157556559721, 360555996724518275, 360555835983925692, 360555754810625961, 360555594193216902, 360555369266045128]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360276333889668828, 360276333950322824⟩, ⟨978175434219749193, 978175579680414811⟩, true⟩

def words02 : List Nat := [360555144466628402, 360554916141931081, 360554730571819845, 360554564179366907, 360554397881318086, 360554162045344139, 360553901746283480, 360553720584356808, 360553539525088518, 360553437513971667]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360330999643963456, 360330999704984228⟩, ⟨784257004466509818, 784257151223726862⟩, true⟩

def words03 : List Nat := [360553359036644630, 360553218594727449, 360553078232305977, 360553016792511475, 360553005202735339, 360552932957185990, 360552860752483867, 360552745206857244, 360552603873130261, 360552541273126524]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360876889265838997, 360876889327224142⟩, ⟨(-1149811186931021171), (-1149811038882074293)⟩, true⟩

def words04 : List Nat := [360552494789186893, 360552565505834244, 360552595694131447, 360552625865401404, 360552634706568107, 360552683178039240, 360552809940527330, 360552936631587113, 360552998893696229, 360553090104784809]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361038161948465368, 361038162010215883⟩, ⟨(-1725299742375198532), (-1725299593027322742)⟩, true⟩

def words05 : List Nat := [360553219356554557, 360553348535578987, 360553432864626799, 360553439350070112, 360553439350106115, 360553377823438699, 360553332790555631, 360553391121403873, 360553527293033312, 360553663388191923]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607109187886268, 360607109250007510⟩, ⟨(-190675393017155047), (-190675242347715701)⟩, true⟩

def words06 : List Nat := [360553759474412090, 360553841065064966, 360553918890616820, 360553996672519061, 360554024846331972, 360554024846370847, 360553975789948117, 360553870625781833, 360553765520540282, 360553713774693112]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359774637828851559, 359774637891339807⟩, ⟨2787425828708201026, 2787425980689739722⟩, true⟩

def words07 : List Nat := [360553806069539836, 360553898312731635, 360553949899736556, 360553949899775562, 360553924546291092, 360553834916437246, 360553745336687296, 360553644078692327, 360553466050195725, 360553248500471020]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360472319921223577, 360472319984080713⟩, ⟨287329294464399728, 287329447768417286⟩, true⟩

def words08 : List Nat := [360553031072239880, 360552890691575386, 360552788785101799, 360552763819282896, 360552738867388249, 360552646614436033, 360552551009916713, 360552475908745115, 360552400849412866, 360552356041954924]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360536689620326491, 360536689683557438⟩, ⟨55569538795573031, 55569693443417555⟩, true⟩

def words09 : List Nat := [360552333754032586, 360552249488924066, 360552165270713329, 360552190645395289, 360552202927155776, 360552215202093783, 360552215202128943, 360552169451160070, 360552129998445331, 360552125709513943]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk035
