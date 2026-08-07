import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk819

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483262762872871, 362483363526016328⟩, ⟨146623534374406309, 152195962868075517⟩, true⟩

def state01 : KState := ⟨⟨362478492534976901, 362478593323361222⟩, ⟨537365755331063306, 542940251184585874⟩, true⟩

def words00 : List Nat := [371285221946189128, 371285221949027659, 371285221909838663, 371285221860952244, 371285221810942942, 371285221807824577, 371285221781954785, 371285221801798232, 371285221818180389, 371285221821117108]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498264727003236, 362498365541054479⟩, ⟨(-1082273649940208595), (-1076697051579682043)⟩, true⟩

def words01 : List Nat := [371285221788001882, 371285221837305276, 371285221984024955, 371285222008072400, 371285222010268719, 371285222011107300, 371285222086295067, 371285222100902875, 371285222263269305, 371285222426937468]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488005606114378, 362488106445798569⟩, ⟨(-241867976406188712), (-236289278065350428)⟩, true⟩

def words02 : List Nat := [371285222562033487, 371285222564870668, 371285222504697231, 371285222511603361, 371285222549002824, 371285222551858023, 371285222478232931, 371285222405322358, 371285222404015603, 371285222442453494]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482040092386893, 362482140957584298⟩, ⟨246975456370347516, 252556245140189580⟩, true⟩

def words03 : List Nat := [371285222628533219, 371285222815737791, 371285223003923792, 371285223013344071, 371285223028898309, 371285223045891934, 371285223210287582, 371285223213126116, 371285223201514076, 371285223167068558]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488500893465646, 362488601784076524⟩, ⟨(-282394021883491080), (-276811150601208594)⟩, true⟩

def words04 : List Nat := [371285223220298923, 371285223258127535, 371285223443619531, 371285223630287693, 371285223790672048, 371285223793510281, 371285223813641711, 371285223875521315, 371285223975738205, 371285224019917439]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491046971989565, 362491147888481831⟩, ⟨(-491034687110902565), (-485449694718854001)⟩, true⟩

def words05 : List Nat := [371285224054117271, 371285224089329696, 371285224272222936, 371285224397854018, 371285224550805916, 371285224704868034, 371285224840518583, 371285224843358269, 371285224877438568, 371285224953247771]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483291931770111, 362483392873572155⟩, ⟨144588081723946764, 150175148636931772⟩, true⟩

def words06 : List Nat := [371285225103289088, 371285225106127954, 371285225074218878, 371285225013762537, 371285224952253205, 371285224908282729, 371285224853043525, 371285224902004176, 371285224945104730, 371285224948094992]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362504532219704792, 362504633187134287⟩, ⟨(-1596565635975753721), (-1590976468251891997)⟩, true⟩

def words07 : List Nat := [371285225054157053, 371285225184070885, 371285225461309995, 371285225587209683, 371285225691288850, 371285225796272428, 371285225955482557, 371285226059876561, 371285226298532443, 371285226538419928]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487361843063702, 362487462836129599⟩, ⟨(-188904340715836899), (-183313071192381829)⟩, true⟩

def words08 : List Nat := [371285226776997592, 371285226832656942, 371285226931138866, 371285227031179052, 371285227163593926, 371285227166433511, 371285227100673226, 371285227035804015, 371285227034942896, 371285227065481694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478828026624819, 362478929045318546⟩, ⟨510822734989859349, 516416105867608583⟩, true⟩

def words09 : List Nat := [371285227101813883, 371285227139279225, 371285227171378177, 371285227174237326, 371285227073272237, 371285226988272242, 371285226948211222, 371285226951100741, 371285226876275398, 371285226802707176]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk819
