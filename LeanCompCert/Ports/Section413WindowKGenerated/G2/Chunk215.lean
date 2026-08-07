import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk215

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586760565181842, 360586763265439854⟩, ⟨(-144624590914921124), (-144585308116157978)⟩, true⟩

def state01 : KState := ⟨⟨360547810698151606, 360547813401052151⟩, ⟨692725266991121241, 692764606617468063⟩, true⟩

def words00 : List Nat := [360580038680408544, 360580037909501775, 360580037353208357, 360580038151271265, 360580038151505854, 360580036747577057, 360580033192071825, 360580028295005336, 360580023398340790, 360580020030834461]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360505313815689591, 360505316521205556⟩, ⟨1606895132008197148, 1606934527905279658⟩, true⟩

def words01 : List Nat := [360580018533846094, 360580016916753731, 360580015299781528, 360580012302576160, 360580008144924328, 360580002721489079, 360579997298475176, 360579994025582109, 360579991669759270, 360579988200011564]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598857197055685, 360598859905191594⟩, ⟨(-406435785344624550), (-406396333053753772)⟩, true⟩

def words02 : List Nat := [360579984730523864, 360579983627401440, 360579985993368335, 360579988359168350, 360579988531318646, 360579988531596310, 360579987418002462, 360579985592060498, 360579984088227476, 360579984965195600]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571511704833889, 360571514415615218⟩, ⟨182583475852512563, 182622985112481589⟩, true⟩

def words03 : List Nat := [360579984965442923, 360579984761875476, 360579985775717382, 360579988555918289, 360579990248555982, 360579991941081669, 360579992553995847, 360579993127410703, 360579993127639931, 360579992734329818]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360528553584778509, 360528556298176959⟩, ⟨1107962198501451313, 1108001764147051891⟩, true⟩

def words04 : List Nat := [360579992577607199, 360579992577885034, 360579990670066490, 360579987428493109, 360579984187175647, 360579979958116979, 360579977451694102, 360579976072953619, 360579974694312408, 360579971693264990]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360611989536941856, 360611992252967792⟩, ⟨(-690778921878858831), (-690739299597777501)⟩, true⟩

def words05 : List Nat := [360579969307735820, 360579967888892112, 360579966470102984, 360579964989835466, 360579962924626449, 360579959042492655, 360579955160665332, 360579953421519026, 360579954251764295, 360579955737982505]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588178301671849, 360588181020342856⟩, ⟨(-177711835835782890), (-177672156513538240)⟩, true⟩

def words06 : List Nat := [360579956146005409, 360579956146283510, 360579954822563797, 360579955231591345, 360579955231824731, 360579954509266229, 360579952657078181, 360579949063362554, 360579945469927153, 360579944399114655]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360526091730778076, 360526094452070292⟩, ⟨1161845726595867358, 1161885462470456542⟩, true⟩

def words07 : List Nat := [360579944399341565, 360579944183457722, 360579943967566759, 360579942177471178, 360579941334363243, 360579939913842179, 360579939211936259, 360579939212214643, 360579937793106774, 360579935298338618]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360649815171263895, 360649817895187669⟩, ⟨(-1508954997297905779), (-1508915204621450217)⟩, true⟩

def words08 : List Nat := [360579932803741493, 360579930249408457, 360579929963296506, 360579930619570384, 360579930619827024, 360579929425796873, 360579927020601488, 360579926752667281, 360579928353230336, 360579931590494906]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578118283614582, 360578121010191627⟩, ⟨39256101917042769, 39295951890941091⟩, true⟩

def words09 : List Nat := [360579933754890802, 360579935919114400, 360579937270698193, 360579940061262239, 360579941358475194, 360579942655609437, 360579942655858028, 360579942570770260, 360579940351131570, 360579940267223616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk215
