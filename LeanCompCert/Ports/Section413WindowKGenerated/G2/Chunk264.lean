import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk264

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552594567507931, 360552598713417579⟩, ⟨796226194862683399, 796300231885982503⟩, true⟩

def state01 : KState := ⟨⟨360568909662525922, 360568913811695963⟩, ⟨365246653575385951, 365320776689339235⟩, true⟩

def words00 : List Nat := [360582760458779685, 360582759789384617, 360582758290849133, 360582755901326989, 360582753511923039, 360582750753599330, 360582748792752143, 360582748262732608, 360582747732715633, 360582746480256711]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612147874109611, 360612152026554826⟩, ⟨(-777204691262294627), (-777130481635203751)⟩, true⟩

def words01 : List Nat := [360582745956797343, 360582744707765310, 360582743458726521, 360582743174350512, 360582741980128019, 360582739533432941, 360582737086855464, 360582736435558911, 360582737549223000, 360582738662880658]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574055636309608, 360574059792053499⟩, ⟨229305332423723129, 229379629218431263⟩, true⟩

def words02 : List Nat := [360582739055133401, 360582739253680925, 360582740880869260, 360582742508039120, 360582743094337026, 360582743094683647, 360582742711752442, 360582741406074056, 360582740100430287, 360582738552145003]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360492371765039296, 360492375924050734⟩, ⟨2388827320379353569, 2388901703552125227⟩, true⟩

def words03 : List Nat := [360582739323879826, 360582740423958900, 360582740424273060, 360582740409443236, 360582738968622258, 360582736655189815, 360582734341831169, 360582733456398849, 360582731145279425, 360582727728269801]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360613468217341176, 360613472379628375⟩, ⟨(-813642788665587542), (-813568318865981844)⟩, true⟩

def words04 : List Nat := [360582724311440528, 360582721949565897, 360582720474317258, 360582719826985017, 360582719179672766, 360582717179746591, 360582715224769324, 360582714225422506, 360582713652657290, 360582714815874038]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360558172646607781, 360558176812207841⟩, ⟨649143485376897698, 649218042817640826⟩, true⟩

def words05 : List Nat := [360582715267618919, 360582715719365468, 360582716134186642, 360582717267306536, 360582717267600586, 360582717058476038, 360582716849329622, 360582715920578532, 360582713568399190, 360582712641490443]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360521471308223314, 360521475477092167⟩, ⟨1620486260942615363, 1620560904892213063⟩, true⟩

def words06 : List Nat := [360582711714526543, 360582711706485772, 360582710789303646, 360582709153218527, 360582707517200717, 360582705242992722, 360582704055372426, 360582702385233964, 360582700715186033, 360582698027333656]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592815843457817, 360592820015603570⟩, ⟨(-268394208229701821), (-268319477524143783)⟩, true⟩

def words07 : List Nat := [360582695714798858, 360582694420390799, 360582693125979566, 360582692480406878, 360582692322636762, 360582690927209666, 360582689531823883, 360582687761703020, 360582687104461463, 360582687487469280]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600629822030496, 360600633997491140⟩, ⟨(-475826894029636330), (-475752075529596166)⟩, true⟩

def words08 : List Nat := [360582687487785769, 360582686616326097, 360582684323860873, 360582682999966090, 360582681676079658, 360582679986565816, 360582678755858502, 360582676800492492, 360582674845199492, 360582674989694923]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360540587188338556, 360540591367072242⟩, ⟨1115204612959186581, 1115279518178735469⟩, true⟩

def words09 : List Nat := [360582676587778054, 360582678185807004, 360582679067122775, 360582679554082751, 360582679554378896, 360582679053978876, 360582679473513091, 360582679473860844, 360582678974477472, 360582677386626157]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk264
