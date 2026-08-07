import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk020

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362813215634822533, 362813215677627722⟩, ⟨(-675336909769308252), (-675336851626535218)⟩, true⟩

def state01 : KState := ⟨⟨362690840573728195, 362690840616985817⟩, ⟨(-429262577385526347), (-429262518335542883)⟩, true⟩

def words00 : List Nat := [371275845927674206, 371275881084770606, 371276161848541851, 371276442332274460, 371276794318428850, 371276911116876644, 371277013627037623, 371277116035164511, 371277277174970731, 371277383372661828]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362519955547158368, 362519955590870365⟩, ⟨(-82727631333221440), (-82727571367633674)⟩, true⟩

def words01 : List Nat := [371277733249802230, 371278082779344806, 371278369884412552, 371278425821491620, 371278524121685221, 371278622324433717, 371278963510403543, 371278981063105310, 371279001347562902, 371279021611965054]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362796240717468004, 362796240761634819⟩, ⟨(-642832367144692286), (-642832306258039028)⟩, true⟩

def words02 : List Nat := [371279215024031722, 371279286005579348, 371279400821918234, 371279515524878809, 371279591424926286, 371279591424977095, 371279346774957750, 371279342684778739, 371279574600863085, 371279730517293097]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362590547302096675, 362590547346728344⟩, ⟨(-223502410998174349), (-223502349165468451)⟩, true⟩

def words03 : List Nat := [371279889253067982, 371280047832701348, 371280370154817210, 371280582194633818, 371280783540401996, 371280984688500297, 371281117721050399, 371281117721101563, 371280987371583790, 371281041051203862]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362256487299039200, 362256487344128154⟩, ⟨459727109991829047, 459727172759782363⟩, true⟩

def words04 : List Nat := [371281241451214364, 371281241451265592, 371281125898873423, 371280997436554589, 371280869099851472, 371280809987768788, 371280699321709002, 371280720013928709, 371280744501518686, 371280744501571951]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362686254564240270, 362686254609795382⟩, ⟨(-423086935803728357), (-423086872077777995)⟩, true⟩

def words05 : List Nat := [371280635161209078, 371280626331432112, 371280842075505094, 371280856737250767, 371280856737290738, 371280827428294720, 371280828547679644, 371280828547737302, 371280872633001262, 371280972284672734]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362202187934727169, 362202187980749659⟩, ⟨574759684399118674, 574759749090258360⟩, true⟩

def words06 : List Nat := [371281060694370509, 371281060694422241, 371280850324364110, 371280860867436489, 371280863480673347, 371280863480725173, 371280557780177087, 371280244677525846, 371279931877514804, 371279849695286016]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361785214705132521, 361785214751624814⟩, ⟨1442735953409623758, 1442736019075657774⟩, true⟩

def words07 : List Nat := [371279743966994280, 371279772282704992, 371279802986198031, 371279802986250190, 371279616320821325, 371279496909832618, 371279426876350462, 371279426876402606, 371279171470697634, 371278837837718881]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362837568136915364, 362837568183875463⟩, ⟨(-751043770260423398), (-751043703618932364)⟩, true⟩

def words08 : List Nat := [371278504525363224, 371278398825200968, 371278185645256981, 371278192747852409, 371278192747892896, 371278164099325972, 371277963837035218, 371277977196221113, 371278217129457698, 371278388985588074]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362532229349076629, 362532229396516299⟩, ⟨(-111840565412091544), (-111840497765822688)⟩, true⟩

def words09 : List Nat := [371278514276335454, 371278639447376223, 371278793320361231, 371278834837349781, 371278940404861550, 371279045871709565, 371279146109218132, 371279146109270900, 371278972016562431, 371278997365214147]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk020
