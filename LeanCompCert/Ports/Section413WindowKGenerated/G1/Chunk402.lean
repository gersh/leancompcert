import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk402

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503333962819159, 362503356903920012⟩, ⟨(-728093501846800907), (-727470317606722415)⟩, true⟩

def state01 : KState := ⟨⟨362468317312851062, 362468340265710796⟩, ⟨679742908605032122, 680366565613406136⟩, true⟩

def words00 : List Nat := [371285261784127600, 371285261785445949, 371285261667960442, 371285261545891511, 371285261423340477, 371285261198806627, 371285260664799767, 371285260644715514, 371285260624150126, 371285260598106057]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505021492372420, 362505044457120613⟩, ⟨(-796294457665443006), (-795670322560165772)⟩, true⟩

def words01 : List Nat := [371285260312435762, 371285260448229637, 371285261201495183, 371285261202813889, 371285261132540784, 371285260905845991, 371285260998487921, 371285261011046617, 371285261503822977, 371285261997147958]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476740354811314, 362476763331493065⟩, ⟨341332452801555668, 341957067933266482⟩, true⟩

def words02 : List Nat := [371285262439904318, 371285262597578307, 371285263066018434, 371285263535133899, 371285264194267656, 371285264195586689, 371285264031634168, 371285263733525322, 371285263434922933, 371285263382895831]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477631941249317, 362477654929820287⟩, ⟨305540072959418598, 306165166455320090⟩, true⟩

def words03 : List Nat := [371285263578783043, 371285263986479319, 371285264393405902, 371285264394725144, 371285263978791414, 371285263680769559, 371285263699855267, 371285263701184878, 371285263595694614, 371285263408111921]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491797885870425, 362491820886269870⟩, ⟨(-264494119063804200), (-263868549530676224)⟩, true⟩

def words04 : List Nat := [371285263648131797, 371285263842875698, 371285264292328341, 371285264742267466, 371285265092288892, 371285265093608712, 371285264689202234, 371285264758872966, 371285265144515543, 371285265308780350]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492685202229362, 362492708214630990⟩, ⟨(-300154534203530299), (-299528481522724911)⟩, true⟩

def words05 : List Nat := [371285265472521107, 371285265636688277, 371285266417120911, 371285266889681653, 371285267482747554, 371285268076312163, 371285268536089713, 371285268537409804, 371285268360007020, 371285268546427947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474759885930819, 362474782910079372⟩, ⟨421612885685385072, 422239411359747162⟩, true⟩

def words06 : List Nat := [371285268991205403, 371285268992526366, 371285268727976184, 371285268463803748, 371285268199102795, 371285268121035984, 371285267860242774, 371285267986124680, 371285268118828236, 371285268120195085]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495091231738146, 362495114267855085⟩, ⟨(-397334037260740748), (-396707029559711054)⟩, true⟩

def words07 : List Nat := [371285267860746676, 371285267669997180, 371285267498062804, 371285267499389855, 371285266932680534, 371285266268650627, 371285265604128972, 371285265556387241, 371285265531759483, 371285265777759018]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484215108218185, 362484238156247849⟩, ⟨40745998086767812, 41373485693380662⟩, true⟩

def words08 : List Nat := [371285265987055921, 371285265988385737, 371285265919454263, 371285266194127079, 371285266500322402, 371285266501643464, 371285265987130077, 371285265469070147, 371285265046911413, 371285265048421922]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362453788477588139, 362453811537517956⟩, ⟨1266903302731871829, 1267531269855165505⟩, true⟩

def words09 : List Nat := [371285265498247687, 371285265974085974, 371285266289114996, 371285266290436500, 371285265784943087, 371285265465693746, 371285265334508074, 371285265335829658, 371285264705342135, 371285263926348109]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk402
