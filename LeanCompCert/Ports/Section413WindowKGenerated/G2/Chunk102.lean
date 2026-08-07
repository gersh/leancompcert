import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk102

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581851552496107, 360581852119613940⟩, ⟨(-12770971037250344), (-12767050052995988)⟩, true⟩

def state01 : KState := ⟨⟨360541331709078327, 360541332277359018⟩, ⟨400561629210973542, 400565562062185718⟩, true⟩

def words00 : List Nat := [360580608265084897, 360580608265208285, 360580606452134076, 360580598788278478, 360580591125905367, 360580577819610095, 360580571895459523, 360580571606717960, 360580571318018787, 360580564947492435]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557055683108832, 360557056252557659⟩, ⟨239923162860818013, 239927107644467335⟩, true⟩

def words01 : List Nat := [360580566826951947, 360580572547523647, 360580577852745725, 360580577852869311, 360580573672836717, 360580560934597610, 360580548198828916, 360580538298400938, 360580534783364608, 360580532486182363]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360520947086038455, 360520947656664426⟩, ⟨608575512619535794, 608579469439461338⟩, true⟩

def words02 : List Nat := [360580530189429927, 360580523018652762, 360580512347609896, 360580511214607190, 360580510081792616, 360580506289368086, 360580493032900581, 360580472513894582, 360580451998877123, 360580437340871607]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360394074266024024, 360394074837815571⟩, ⟨1907571306610426608, 1907575275360166180⟩, true⟩

def words03 : List Nat := [360580431526322390, 360580428285487172, 360580425045272998, 360580416794272182, 360580413941023648, 360580405427360160, 360580396915324227, 360580393020675783, 360580379679504028, 360580361485799963]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360528725438494873, 360528726011458483⟩, ⟨527581134772987372, 527585115530401968⟩, true⟩

def words04 : List Nat := [360580343295623891, 360580318401641124, 360580298532997064, 360580288164789341, 360580277798595412, 360580259460430479, 360580235658108844, 360580221352610644, 360580207049865917, 360580197730046815]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360531912227383886, 360531912801529993⟩, ⟨494684219375793031, 494688212259638811⟩, true⟩

def words05 : List Nat := [360580192709017456, 360580180309560102, 360580167912497155, 360580166836392372, 360580166836498075, 360580162223518335, 360580157611425135, 360580146903499828, 360580132726551368, 360580128026896430]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360633754987812379, 360633755563130325⟩, ⟨(-550900544527795682), (-550896539614953822)⟩, true⟩

def words06 : List Nat := [360580123707139294, 360580124525155890, 360580124525267338, 360580118102532856, 360580111681029635, 360580102733262211, 360580107614742370, 360580114784143122, 360580114784256792, 360580119447891794]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360872889284651730, 360872889861142697⟩, ⟨(-3007850095129559186), (-3007846078163831588)⟩, true⟩

def words07 : List Nat := [360580134123576871, 360580148796440861, 360580172918576450, 360580195770312586, 360580210289389589, 360580224805652793, 360580244610823126, 360580269364934514, 360580297830064295, 360580326289684295]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360721860533443104, 360721861111120964⟩, ⟨(-1455707295962798177), (-1455703266790096609)⟩, true⟩

def words08 : List Nat := [360580348403490086, 360580365762299781, 360580379020915312, 360580392276986539, 360580397259577089, 360580397751623862, 360580397751735943, 360580393142142369, 360580393349384162, 360580407096274001]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360477156773866063, 360477157352717415⟩, ⟨1063824258889639968, 1063828300143457518⟩, true⟩

def words09 : List Nat := [360580425716045512, 360580444332222793, 360580457392344510, 360580461119588394, 360580461119692901, 360580459851456497, 360580458583429356, 360580456895318712, 360580451682148840, 360580441653702217]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk102
