import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk106

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362441443158411242, 362441444580514751⟩, ⟨464154951246997718, 464165156360841734⟩, true⟩

def state01 : KState := ⟨⟨362537209461062632, 362537210885956686⟩, ⟨(-551138715198086633), (-551128480490581267)⟩, true⟩

def words00 : List Nat := [371285234379913186, 371285236121312848, 371285244119005088, 371285252115313786, 371285257545609887, 371285257545921519, 371285253640415684, 371285256129084149, 371285266636766228, 371285271532409369]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484984787601435, 362484986215336848⟩, ⟨3706271303442957, 3716536172258039⟩, true⟩

def words01 : List Nat := [371285276306858714, 371285281080513158, 371285294727732754, 371285305003795152, 371285315780485650, 371285326555265849, 371285337280130668, 371285337280442678, 371285336204232417, 371285336171661920]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362443693508466237, 362443694938985595⟩, ⟨442402716777712646, 442413011226365076⟩, true⟩

def words02 : List Nat := [371285339686481097, 371285339686793359, 371285333704958957, 371285327679543208, 371285321655139648, 371285316435707970, 371285310898148318, 371285312557113331, 371285314224760797, 371285314225084031]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362564385914406302, 362564387347759431⟩, ⟨(-841136664453995804), (-841126339868057462)⟩, true⟩

def words03 : List Nat := [371285315246464067, 371285320181977085, 371285328296702380, 371285328297016451, 371285328170350410, 371285326693354432, 371285328097772334, 371285328098119934, 371285334119966902, 371285341549444606]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468969035795407, 362468970471968866⟩, ⟨174427084223682742, 174437438832596780⟩, true⟩

def words04 : List Nat := [371285348923224971, 371285348923538600, 371285352294373095, 371285357127836704, 371285364578375192, 371285364578688151, 371285360289558606, 371285354643192916, 371285349573850044, 371285349574206669]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362458273049195645, 362458274488187539⟩, ⟨288941717463187792, 288952102102673392⟩, true⟩

def words05 : List Nat := [371285355314123318, 371285362590596502, 371285369150786934, 371285369151105355, 371285370427031134, 371285372373535714, 371285383127035776, 371285383231582076, 371285383231819434, 371285380689135257]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362537937371201793, 362537938813000894⟩, ⟨(-560657052653701772), (-560646638074908022)⟩, true⟩

def words06 : List Nat := [371285379172967156, 371285379173312024, 371285381294309856, 371285386753151441, 371285391050521409, 371285391050834873, 371285385047051720, 371285386441656578, 371285394610418019, 371285399534763156]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362532143828525071, 362532145273183723⟩, ⟨(-498751808144879790), (-498741363040259786)⟩, true⟩

def words07 : List Nat := [371285404407706794, 371285409279847096, 371285419768309393, 371285425917232999, 371285432222076963, 371285438525853177, 371285444786546091, 371285444786860643, 371285446643295305, 371285451015807049]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362516676933954831, 362516678381414129⟩, ⟨(-333304485280978893), (-333294010250717295)⟩, true⟩

def words08 : List Nat := [371285459753987482, 371285461706812322, 371285463684629848, 371285465662177383, 371285470265297911, 371285471615893500, 371285481715861166, 371285491814070168, 371285500269746676, 371285503186366826]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362591116473413098, 362591117923712158⟩, ⟨(-1129331281106335235), (-1129320775704845713)⟩, true⟩

def words09 : List Nat := [371285514849159894, 371285526509935584, 371285542231845174, 371285546319965056, 371285548777367133, 371285551234414992, 371285559818457044, 371285564060570616, 371285573925632673, 371285583788985979]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk106
