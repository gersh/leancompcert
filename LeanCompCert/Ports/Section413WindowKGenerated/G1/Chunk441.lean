import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk441

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482117486624125, 362482145303145924⟩, ⟨149635278384425209, 150464121387536429⟩, true⟩

def state01 : KState := ⟨⟨362468163291582161, 362468191121067455⟩, ⟨765122075489161647, 765951490251498663⟩, true⟩

def words00 : List Nat := [371285557548459809, 371285557549917565, 371285557302637236, 371285557021675836, 371285556740156267, 371285556614204571, 371285556231719441, 371285556063558172, 371285555894942662, 371285555698039831]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362523612996640902, 362523640839313634⟩, ⟨(-1681037031075902005), (-1680207034548970153)⟩, true⟩

def words01 : List Nat := [371285555425699107, 371285555547782745, 371285556088623782, 371285556296314258, 371285556364098739, 371285556432318019, 371285556960690635, 371285557311784692, 371285558175955073, 371285559040747216]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362510223916491499, 362510251772334284⟩, ⟨(-1090323785604684012), (-1089493207946572624)⟩, true⟩

def words02 : List Nat := [371285559740009962, 371285559951417978, 371285560676000927, 371285561401289467, 371285562268284722, 371285562451234038, 371285562630850428, 371285562810988350, 371285563504005728, 371285564065100218]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485240814264221, 362485268683224012⟩, ⟨12418531837260947, 13249688416269843⟩, true⟩

def words03 : List Nat := [371285565138991455, 371285566213428498, 371285567269831875, 371285567642321614, 371285567979716769, 371285568317822642, 371285568865752530, 371285568867213010, 371285568862582348, 371285568857406529]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481653863342137, 362481681745381726⟩, ⟨170883128188660833, 171714862176282995⟩, true⟩

def words04 : List Nat := [371285569243194327, 371285569450242828, 371285569920570548, 371285570391483286, 371285570795259392, 371285570796718898, 371285570685747947, 371285570856724201, 371285571095220874, 371285571096733398]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490153528950120, 362490181424302528⟩, ⟨(-204384790488823343), (-203552468675585231)⟩, true⟩

def words05 : List Nat := [371285571009732677, 371285570922334483, 371285571184834567, 371285571358976513, 371285571687675532, 371285572016935370, 371285572293091768, 371285572294551626, 371285571991568002, 371285572097777414]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469353109681090, 362469381018045074⟩, ⟨714245514212709592, 715078410685451164⟩, true⟩

def words06 : List Nat := [371285572464230038, 371285572465690207, 371285572220731050, 371285571879550558, 371285571537847307, 371285571221086488, 371285570694121172, 371285570546804952, 371285570398990329, 371285570250797745]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362511311966358624, 362511339887905388⟩, ⟨(-1139257233244767417), (-1138423754422138559)⟩, true⟩

def words07 : List Nat := [371285570031219735, 371285570178904906, 371285570772896052, 371285570880340030, 371285570974200972, 371285571068536852, 371285571376190095, 371285571448826011, 371285572033077505, 371285572617938160]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479132023736975, 362479159958468007⟩, ⟨282516835073989135, 283350896445706761⟩, true⟩

def words08 : List Nat := [371285573199260864, 371285573200721527, 371285573199870817, 371285573302287408, 371285573558997137, 371285573560457893, 371285573134685713, 371285572606907292, 371285572078572681, 371285572062936116]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477754195159325, 362477782143081421⟩, ⟨343403128920686811, 344237773270950055⟩, true⟩

def words09 : List Nat := [371285571918845303, 371285571912499364, 371285571905640932, 371285571898402094, 371285571364009911, 371285570985447059, 371285570682633067, 371285570684130585, 371285570502536283, 371285570327997054]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk441
