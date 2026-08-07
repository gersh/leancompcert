import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk013

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360036169095275369, 360036169102553667⟩, ⟨644261078753499468, 644261085202521702⟩, true⟩

def state01 : KState := ⟨⟨361122812769559067, 361122812776957550⟩, ⟨(-767236774426881848), (-767236767821016778)⟩, true⟩

def words00 : List Nat := [360531567879082468, 360532210247464871, 360533425366415909, 360534638623118061, 360535337564725473, 360535471988109106, 360536177333127674, 360536881600464572, 360537135854943587, 360537582595553266]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360485035996797336, 360485036004318368⟩, ⟨69911303195769485, 69911309962789563⟩, true⟩

def words01 : List Nat := [360537618240800710, 360537653831753647, 360537767607849457, 360538190897865994, 360538440349547998, 360538689422414221, 360538689422425742, 360538641082978485, 360538039271902456, 360537999117926542]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361120919800426933, 361120919808070022⟩, ⟨(-776380878521548798), (-776380871592796938)⟩, true⟩

def words02 : List Nat := [360538478908376309, 360538478908389226, 360538446074740427, 360537974419270721, 360537503475731777, 360536822951539172, 360536867027660766, 360537166668913907, 360537174791821204, 360537613368105487]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361219551909125070, 361219551916891312⟩, ⟨(-908745909483668786), (-908745902390493042)⟩, true⟩

def words03 : List Nat := [360538141377207367, 360538668594101297, 360539374941068969, 360540023678289368, 360540186085708493, 360540348250185674, 360540456125059520, 360540876859069824, 360541383333004260, 360541889051574017]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360457215649973408, 360457215657865084⟩, ⟨112886172665277812, 112886179927170302⟩, true⟩

def words04 : List Nat := [360542086496461770, 360542303990086181, 360542618713578185, 360542932969083816, 360543080328005186, 360543080328018369, 360542695372837006, 360542028998053629, 360541363611221541, 360540835050403729]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨358749902680713536, 358749902688730692⟩, ⟨2424941968231837966, 2424941975663774752⟩, true⟩

def words05 : List Nat := [360540773155971624, 360540667157604826, 360540561315923075, 360539994429326988, 360538900936130839, 360537650333867511, 360536401574787293, 360535281286498530, 360534260286703468, 360532948259071703]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360105085529024750, 360105085537168808⟩, ⟨575964074009376917, 575964081614541213⟩, true⟩

def words06 : List Nat := [360531638159471741, 360530852463122107, 360530365559340675, 360530045836959244, 360529726583034670, 360528917399141353, 360527592138307814, 360526786364545680, 360525981767950933, 360525497275573583]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359751052164192527, 359751052172465722⟩, ⟨1064473552893687744, 1064473560676413796⟩, true⟩

def words07 : List Nat := [360525190629532844, 360524613769941464, 360524037750638118, 360524202021237903, 360524202021249361, 360524087891629861, 360523973927774654, 360523495201779366, 360522969185268625, 360522409825129790]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨359929313190502514, 359929313198904048⟩, ⟨816794348690238658, 816794356650729130⟩, true⟩

def words08 : List Nat := [360521851275066499, 360521800941213089, 360521247575325977, 360520430643749443, 360519614891855339, 360518654639919152, 360518180242193792, 360517850989957608, 360517522211805276, 360516935038221120]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360517311008598450, 360517311017129812⟩, ⟨(-6965126602781780), (-6965118461170710)⟩, true⟩

def words09 : List Nat := [360516512592625331, 360516190865054322, 360515869599400045, 360515522574791744, 360515156690617032, 360514367161873606, 360513578763448030, 360512820314800260, 360512335932500249, 360512339483610062]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk013
