import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk238

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617030334506735, 360617033673410222⟩, ⟨(-834320672852771860), (-834266911202132032)⟩, true⟩

def state01 : KState := ⟨⟨360628004456307237, 360628007798132464⟩, ⟨(-1095372049306568074), (-1095318218103561868)⟩, true⟩

def words00 : List Nat := [360581985149124130, 360581989265906347, 360581993888417751, 360581998510600747, 360582001486148800, 360582002710768661, 360582003289901113, 360582003869070729, 360582005352700532, 360582007285003929]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360624912256998436, 360624915601774092⟩, ⟨(-1021684928740314405), (-1021631027273102235)⟩, true⟩

def words01 : List Nat := [360582008332850255, 360582009380642315, 360582012188015582, 360582016350761186, 360582019343583233, 360582022336204113, 360582024127060803, 360582024168814839, 360582025969713581, 360582027770563266]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611300980465593, 360611304328164793⟩, ⟨(-697631582735459648), (-697577611615079438)⟩, true⟩

def words02 : List Nat := [360582028947936173, 360582029087939726, 360582029088218518, 360582028331769489, 360582027575333858, 360582026545910082, 360582028503409442, 360582030460809485, 360582031243009206, 360582032471691499]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360696315501029068, 360696318851653106⟩, ⟨(-2723902398711951907), (-2723848357878137325)⟩, true⟩

def words03 : List Nat := [360582035458057358, 360582038444266131, 360582043187840006, 360582047372781791, 360582049827429793, 360582052281891290, 360582054906897923, 360582058674149125, 360582063467193021, 360582068259904516]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360677803186257643, 360677806539842546⟩, ⟨(-2282530190599074024), (-2282476079163812082)⟩, true⟩

def words04 : List Nat := [360582072161248081, 360582076891887260, 360582082952946085, 360582089013587024, 360582094195895031, 360582097633004049, 360582100187620405, 360582102742058364, 360582105236375845, 360582109249197969]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360564829759460597, 360564833115968021⟩, ⟨412455773166123320, 412509954318463944⟩, true⟩

def words05 : List Nat := [360582112869497425, 360582116489551542, 360582119227981666, 360582120222277047, 360582120225136851, 360582120228082908, 360582121984897307, 360582122605885863, 360582122606166910, 360582121881865694]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360642151900238582, 360642155259683619⟩, ⟨(-1432992945855529680), (-1432938694598197100)⟩, true⟩

def words06 : List Nat := [360582121673462865, 360582123433186225, 360582125118107154, 360582126802942369, 360582126805928674, 360582126806239278, 360582125066785840, 360582124231539063, 360582124312785539, 360582126827921306]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360643349529140413, 360643352891539126⟩, ⟨(-1461543614287771950), (-1461489292511277922)⟩, true⟩

def words07 : List Nat := [360582128391657172, 360582129955295851, 360582133270386407, 360582137725187810, 360582141646603472, 360582145567741047, 360582148121345373, 360582148933795090, 360582151497026383, 360582154060145497]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588216200969341, 360588219566294959⟩, ⟨(-144996057062790393), (-144941665376718817)⟩, true⟩

def words08 : List Nat := [360582155980372759, 360582156159817881, 360582156160095491, 360582155245530658, 360582154330987265, 360582152392537555, 360582152021696835, 360582152711561565, 360582152711838692, 360582152776902439]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360672713320061305, 360672716688326941⟩, ⟨(-2164292823160471015), (-2164238361223078785)⟩, true⟩

def words09 : List Nat := [360582152970844033, 360582153164858058, 360582155108019077, 360582156568275914, 360582156568565586, 360582156430223917, 360582156951241034, 360582158992400797, 360582162781677452, 360582166570707466]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk238
