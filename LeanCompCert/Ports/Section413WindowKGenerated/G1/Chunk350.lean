import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk350

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492990413479372, 362493007607063257⟩, ⟨(-282031463139816316), (-281624756683788498)⟩, true⟩

def state01 : KState := ⟨⟨362468041453252889, 362468058657090506⟩, ⟨591270241864342927, 591677307254113063⟩, true⟩

def words00 : List Nat := [371284961649087833, 371284961650232641, 371284961315707956, 371284961277724976, 371284961451550754, 371284961452688741, 371284960792835297, 371284959981157202, 371284959169051750, 371284958894372829]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362452051093101499, 362452068307150911⟩, ⟨1151318430081888840, 1151725853039874644⟩, true⟩

def words01 : List Nat := [371284958617323032, 371284958823424898, 371284958878126488, 371284958879283461, 371284958377123962, 371284958030626703, 371284957836546512, 371284957837683269, 371284956905014909, 371284955967146339]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478719800581481, 362478737024825631⟩, ⟨217284973479435607, 217692753508276821⟩, true⟩

def words02 : List Nat := [371284955028847353, 371284954427693384, 371284953519855155, 371284953427390463, 371284953334555433, 371284953131499869, 371284951965833019, 371284951615571793, 371284951489919772, 371284951491097635]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362464600288527301, 362464617523134511⟩, ⟨712032740428943053, 712440883527319017⟩, true⟩

def words03 : List Nat := [371284951314548855, 371284951135285187, 371284951478851087, 371284951598441381, 371284951618814089, 371284951639589425, 371284951640449995, 371284951522505308, 371284950318979808, 371284949740130154]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362461172156392737, 362461189401143851⟩, ⟨832268730336513589, 832677228929757141⟩, true⟩

def words04 : List Nat := [371284949265300471, 371284949266457695, 371284948697566799, 371284948126214376, 371284947554470304, 371284947141763814, 371284946453393183, 371284946433099446, 371284946412422304, 371284946240770949]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362513359255657373, 362513376510675422⟩, ⟨(-997108721897814458), (-996699863395812470)⟩, true⟩

def words05 : List Nat := [371284945699448585, 371284945836475266, 371284946786295425, 371284946910937001, 371284946911827866, 371284946902204987, 371284947294246816, 371284947295500052, 371284948104862101, 371284948916956025]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489418017450966, 362489435282747807⟩, ⟨(-157737450020312595), (-157328231091381051)⟩, true⟩

def words06 : List Nat := [371284949706554000, 371284949707692557, 371284949772799073, 371284949974090644, 371284950425917430, 371284950427055851, 371284949909787673, 371284949389958174, 371284949161351036, 371284949290586438]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362459026726492115, 362459044002046092⟩, ⟨908399692027596232, 908809270726560704⟩, true⟩

def words07 : List Nat := [371284949925643925, 371284950561141707, 371284951192953075, 371284951276805432, 371284951435847464, 371284951595428242, 371284952089928426, 371284952091067427, 371284951502987084, 371284950765749814]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502813047673722, 362502830333426967⟩, ⟨(-627793348884942287), (-627383412344554993)⟩, true⟩

def words08 : List Nat := [371284950101649442, 371284950102915466, 371284950251026722, 371284950731928150, 371284951080363088, 371284951081502547, 371284950472884263, 371284950401031115, 371284951067139363, 371284951577838795]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362522303143161490, 362522320439297961⟩, ⟨(-1311856401049673193), (-1311446100110920839)⟩, true⟩

def words09 : List Nat := [371284951906639691, 371284952235773847, 371284953157833999, 371284953676651613, 371284954445794756, 371284955215340352, 371284955981415610, 371284956235842672, 371284957301123265, 371284958366989169]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk350
