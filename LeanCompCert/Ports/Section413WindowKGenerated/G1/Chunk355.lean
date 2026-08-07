import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk355

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362442037076827047, 362442054785907216⟩, ⟨1524823768611766060, 1525248646679272050⟩, true⟩

def state01 : KState := ⟨⟨362477796897879771, 362477814617277217⟩, ⟨255205101336240764, 255630345719758670⟩, true⟩

def words00 : List Nat := [371285018327059807, 371285017822611207, 371285016954415559, 371285016613763676, 371285016272744477, 371285015802251889, 371285014419457946, 371285013830304488, 371285013443053410, 371285013444247642]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478402091232443, 362478419821168303⟩, ⟨233709704882780204, 234135323537337690⟩, true⟩

def words01 : List Nat := [371285013242405728, 371285012867024694, 371285012611676393, 371285012612958693, 371285012337568442, 371285012305598019, 371285012273244714, 371285012237986159, 371285011652925372, 371285011468790413]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477855314641462, 362477873054845712⟩, ⟨253120633145920427, 253546616587137233⟩, true⟩

def words02 : List Nat := [371285011890646623, 371285011891800553, 371285011443518846, 371285010999933406, 371285010555957664, 371285010078563681, 371285009263168117, 371285009240227093, 371285009216891953, 371285009182528998]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362519537356960710, 362519555107592669⟩, ⟨(-1227976408560118708), (-1227550054569587182)⟩, true⟩

def words03 : List Nat := [371285009573486232, 371285010165875030, 371285011549410605, 371285011998197540, 371285012245380954, 371285012492923493, 371285013531639872, 371285014177105198, 371285015149791212, 371285016122911046]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362508388086106198, 362508405847160544⟩, ⟨(-831738733733583536), (-831312009277641506)⟩, true⟩

def words04 : List Nat := [371285016926884648, 371285016975598989, 371285017815393886, 371285018655748787, 371285019738136657, 371285020165109221, 371285020431119369, 371285020697491160, 371285021541771873, 371285022200869930]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490802029041376, 362490819800520224⟩, ⟨(-206353709863313488), (-205926614763597500)⟩, true⟩

def words05 : List Nat := [371285023566056470, 371285024931660092, 371285026146449015, 371285026511870888, 371285027006846884, 371285027502348526, 371285028510722968, 371285028673292574, 371285028837020122, 371285029001196145]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489278592827640, 362489296374646380⟩, ⟨(-152112529998353377), (-151685067160016399)⟩, true⟩

def words06 : List Nat := [371285029810710418, 371285030227471170, 371285030913964567, 371285031600876194, 371285032161568784, 371285032162724341, 371285031670036481, 371285031505034819, 371285031963353109, 371285032084433566]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498041298211314, 362498059090532176⟩, ⟨(-463777239827810282), (-463349403374964228)⟩, true⟩

def words07 : List Nat := [371285032159544963, 371285032235031590, 371285033100327434, 371285033753337116, 371285034629796780, 371285035506658546, 371285036266246041, 371285036267401813, 371285036340284935, 371285036707704966]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362448599189831059, 362448616992466242⟩, ⟨1295566478421302888, 1295994681910636638⟩, true⟩

def words08 : List Nat := [371285037077357560, 371285037078513572, 371285036395895074, 371285035653635029, 371285034910963521, 371285034209038776, 371285033115553424, 371285032600475469, 371285032085023865, 371285031566276600]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362515013695707605, 362515031508800396⟩, ⟨(-1068426568215356325), (-1067997992487379275)⟩, true⟩

def words09 : List Nat := [371285030543921300, 371285030311629259, 371285030634437336, 371285030635599772, 371285030526756277, 371285030261567613, 371285030518735156, 371285030720372021, 371285031563875589, 371285032407862575]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk355
