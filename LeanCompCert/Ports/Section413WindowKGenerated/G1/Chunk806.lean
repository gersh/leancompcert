import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk806

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480113748888941, 362480211218515286⟩, ⟨393490340683666697, 398795164354943165⟩, true⟩

def state01 : KState := ⟨⟨362468882083597347, 362468979578346934⟩, ⟨1298780351335081652, 1304087200068135430⟩, true⟩

def words00 : List Nat := [371285158990036031, 371285158918248202, 371285158656504460, 371285158550008349, 371285158442170899, 371285158340769463, 371285158060410022, 371285157766848040, 371285157472098489, 371285157313120140]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362459152480882755, 362459250000736957⟩, ⟨2083211803395233505, 2088520675941058567⟩, true⟩

def words01 : List Nat := [371285157114322176, 371285157070458992, 371285157025658730, 371285156976477506, 371285156769032670, 371285156582503581, 371285156394512562, 371285156321276671, 371285156057935181, 371285155739709186]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485860609435561, 362485958154249796⟩, ⟨(-70126328480058724), (-64815443526847996)⟩, true⟩

def words02 : List Nat := [371285155420272973, 371285155255793993, 371285155013072196, 371285154890944707, 371285154767918827, 371285154622010228, 371285154385089871, 371285154303302117, 371285154288717189, 371285154301593537]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482778599844691, 362482876170158928⟩, ⟨178396500439128849, 183709441576595053⟩, true⟩

def words03 : List Nat := [371285154303705306, 371285154302251471, 371285154358857027, 371285154361930854, 371285154387201885, 371285154425536020, 371285154463041888, 371285154465835129, 371285154337693914, 371285154313035622]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465223885000661, 362465321480115174⟩, ⟨1594119727678454475, 1599434668841957673⟩, true⟩

def words04 : List Nat := [371285154337269044, 371285154340058879, 371285154208436331, 371285154077842597, 371285153946208983, 371285153856700743, 371285153689118672, 371285153558137087, 371285153426207113, 371285153280100816]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493826587701594, 362493924208012896⟩, ⟨(-712824746036223148), (-707507772625539766)⟩, true⟩

def words05 : List Nat := [371285153036096202, 371285152947167393, 371285152888803648, 371285152891642858, 371285152798441617, 371285152695151569, 371285152637930877, 371285152641034121, 371285152722475140, 371285152834330131]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478477460741126, 362478575106241925⟩, ⟨525249825502996028, 530568830829022430⟩, true⟩

def words06 : List Nat := [371285152907198605, 371285152909990841, 371285152809608556, 371285152789513163, 371285152768028364, 371285152756482426, 371285152562328693, 371285152368720264, 371285152173952172, 371285152134019650]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486759278478036, 362486856949127828⟩, ⟨(-142844637631538054), (-137523603409254700)⟩, true⟩

def words07 : List Nat := [371285152126390453, 371285152201463941, 371285152275680795, 371285152278496509, 371285152249641252, 371285152231069873, 371285152342643122, 371285152366438983, 371285152389652706, 371285152413940991]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362497068797552374, 362497166493208918⟩, ⟨(-974595445966264364), (-969272394072488826)⟩, true⟩

def words08 : List Nat := [371285152590454042, 371285152725305022, 371285153012399208, 371285153300601551, 371285153537447199, 371285153570234899, 371285153755601127, 371285153942449684, 371285154191470898, 371285154343228469]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490492550478455, 362490590271537885⟩, ⟨(-443892379451446518), (-438567277670332158)⟩, true⟩

def words09 : List Nat := [371285154491848037, 371285154641371514, 371285154879284965, 371285155042000464, 371285155250898639, 371285155460960475, 371285155655301855, 371285155660107493, 371285155729350040, 371285155800122781]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk806
