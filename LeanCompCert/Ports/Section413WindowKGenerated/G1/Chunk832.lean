import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk832

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481803841776690, 362481907955163502⟩, ⟨277917553227743603, 283766550846933099⟩, true⟩

def state01 : KState := ⟨⟨362487875068955747, 362487979208181078⟩, ⟨(-227201156751701816), (-221350009234736498)⟩, true⟩

def words00 : List Nat := [371285318599946753, 371285318603182537, 371285318705591662, 371285318831180552, 371285318933756532, 371285318936641649, 371285318898658155, 371285318954396835, 371285319068079582, 371285319103035909]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482616941984286, 362482721107478580⟩, ⟨210357925721288668, 216211259208882982⟩, true⟩

def words01 : List Nat := [371285319136924338, 371285319171760614, 371285319271057542, 371285319316056443, 371285319335157538, 371285319355437229, 371285319374422578, 371285319377308133, 371285319203631124, 371285319175962225]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485201119569970, 362485305310792210⟩, ⟨(-4720394339264346), 1135080360652980⟩, true⟩

def words02 : List Nat := [371285319259889058, 371285319262774865, 371285319185728373, 371285319080892646, 371285318974930038, 371285318912546781, 371285318855347664, 371285318901069946, 371285318945623374, 371285318948667504]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490987422629486, 362491091639967013⟩, ⟨(-486291900033423255), (-480434251628131121)⟩, true⟩

def words03 : List Nat := [371285319094674514, 371285319242423729, 371285319532961346, 371285319632023219, 371285319715808847, 371285319800463354, 371285319880695772, 371285319890091036, 371285319961401204, 371285320034008073]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478498276673331, 362478602520080541⟩, ⟨553348446698811045, 559208265273681057⟩, true⟩

def words04 : List Nat := [371285320105617497, 371285320108504356, 371285320008938473, 371285320033829774, 371285320101352060, 371285320104239268, 371285319995047085, 371285319886680704, 371285319777086901, 371285319736480225]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472524672648634, 362472628942044145⟩, ⟨1050693957645385854, 1056555939881394368⟩, true⟩

def words05 : List Nat := [371285319657786801, 371285319641009590, 371285319623269096, 371285319606053294, 371285319395674752, 371285319230851585, 371285319064509236, 371285319043441894, 371285318929572846, 371285318780380458]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495395601623379, 362495499896864883⟩, ⟨(-853649427315859655), (-847785293011930079)⟩, true⟩

def words06 : List Nat := [371285318629928406, 371285318611049612, 371285318548504591, 371285318581213677, 371285318588525495, 371285318591423831, 371285318516064821, 371285318552990348, 371285318732656114, 371285318857931618]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497227348482294, 362497331670077883⟩, ⟨(-1006160471691410868), (-1000294142748708286)⟩, true⟩

def words07 : List Nat := [371285318971909628, 371285319086940231, 371285319344945106, 371285319532225677, 371285319760741291, 371285319990329588, 371285320215549542, 371285320303345314, 371285320449567125, 371285320597411264]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484371116699639, 362484475464005657⟩, ⟨64558857265655593, 70427327507714761⟩, true⟩

def words08 : List Nat := [371285320800787497, 371285320812895030, 371285320815063686, 371285320797266051, 371285320801543200, 371285320804812370, 371285320859479971, 371285320944665879, 371285321028640426, 371285321031630915]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491979473249782, 362492083846691504⟩, ⟨(-569216743800624385), (-563346096587585721)⟩, true⟩

def words09 : List Nat := [371285321083159407, 371285321146318138, 371285321252653543, 371285321255542451, 371285321170019579, 371285321061999258, 371285320961724957, 371285320964908733, 371285320985100721, 371285321069574932]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk832
