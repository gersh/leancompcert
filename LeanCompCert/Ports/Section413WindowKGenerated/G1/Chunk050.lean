import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk050

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362629785529113985, 362629785823676740⟩, ⟨(-753345050607259568), (-753344052353052624)⟩, true⟩

def state01 : KState := ⟨⟨362479869188217687, 362479869484020818⟩, ⟨(-3546900505157377), (-3545896042619811)⟩, true⟩

def words00 : List Nat := [371279177496766152, 371279177496903806, 371279192588616144, 371279219990870138, 371279242542687034, 371279242542824771, 371279212202371227, 371279182157070586, 371279161720182923, 371279161861581661]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362382599693762967, 362382599990809449⟩, ⟨485288152147836555, 485289162845954767⟩, true⟩

def words01 : List Nat := [371279201598494503, 371279241319610537, 371279279885332594, 371279279885470799, 371279278332784000, 371279276564663163, 371279300960137073, 371279300960275831, 371279290399670815, 371279271138786731]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362620164750233247, 362620165048516997⟩, ⟨(-707587470151648713), (-707586453236044219)⟩, true⟩

def words02 : List Nat := [371279272120842414, 371279274859153380, 371279317061686914, 371279359247480914, 371279393418524021, 371279395369286708, 371279417238257063, 371279439098598965, 371279491797233449, 371279519758666860]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362652157304648631, 362652157604199711⟩, ⟨(-868865928240894445), (-868864904944422351)⟩, true⟩

def words03 : List Nat := [371279547249225064, 371279574728905682, 371279618212469059, 371279641921942549, 371279673625242073, 371279705316004619, 371279734597619653, 371279734597759293, 371279763773676404, 371279797972193280]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362415363767914190, 362415364068700668⟩, ⟨326418806087174008, 326419835616558924⟩, true⟩

def words04 : List Nat := [371279866976145623, 371279883785830316, 371279897205789653, 371279910620474744, 371279935481734739, 371279944451442822, 371279967405967886, 371279990351455728, 371280001659768092, 371280001659911868]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362828792679222592, 362828792981263936⟩, ⟨(-1763259834581937364), (-1763258798709066664)⟩, true⟩

def words05 : List Nat := [371280015123120925, 371280041372994621, 371280097521735207, 371280128050231217, 371280151684604641, 371280175309675772, 371280224012768895, 371280253981466332, 371280322862786228, 371280391716946792]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362642179927718441, 362642180231016256⟩, ⟨(-818872301343193260), (-818871259106044960)⟩, true⟩

def words06 : List Nat := [371280452416628567, 371280461331026243, 371280501051027650, 371280540755417346, 371280591878764383, 371280604464870403, 371280616086278028, 371280627703147410, 371280667161999858, 371280699012498007]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362445584894891556, 362445585199445180⟩, ⟨179401904445566565, 179402953056142611⟩, true⟩

def words07 : List Nat := [371280750499062564, 371280801965386191, 371280851361918587, 371280858792698558, 371280864560238457, 371280870325572810, 371280914726454878, 371280914726594462, 371280907694474824, 371280900741385366]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362505528139315118, 362505528445120914⟩, ⟨(-124519916636900823), (-124518861658957275)⟩, true⟩

def words08 : List Nat := [371280925413939061, 371280946601282856, 371280977324033770, 371281008034755480, 371281034235701873, 371281034235841618, 371281022594525831, 371281036022474167, 371281065014395009, 371281069819770501]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505987264543182, 362505987571621927⟩, ⟨(-126754274409696136), (-126753212945985158)⟩, true⟩

def words09 : List Nat := [371281074751613765, 371281079681566314, 371281104160131631, 371281110165243441, 371281127555945166, 371281144939880601, 371281162532673689, 371281162532813710, 371281134000284387, 371281138872749945]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk050
