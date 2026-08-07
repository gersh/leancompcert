import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk415

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467408879549430, 362467433391363480⟩, ⟨733214965119225837, 733902319030888281⟩, true⟩

def state01 : KState := ⟨⟨362468505982826366, 362468530506863926⟩, ⟨687716100706066441, 688403961957418419⟩, true⟩

def words00 : List Nat := [371285117418399052, 371285117419901914, 371285117189545796, 371285117028878523, 371285116867775430, 371285116618426067, 371285115595780425, 371285115153708453, 371285114710956913, 371285114557983113]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473155743953718, 362473180280428143⟩, ⟨494723453960166656, 495411831527851656⟩, true⟩

def words01 : List Nat := [371285114159493680, 371285113718791225, 371285113415101423, 371285113416619777, 371285113396209303, 371285113408445803, 371285113409493645, 371285113316355429, 371285112450292292, 371285112164617157]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468438239953929, 362468462788582426⟩, ⟨690691709041417308, 691380591310064034⟩, true⟩

def words02 : List Nat := [371285112170353866, 371285112171725509, 371285111913244945, 371285111655010611, 371285111396261099, 371285111140750521, 371285110598225902, 371285110578395284, 371285110558091764, 371285110527357049]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500833853845639, 362500858414825651⟩, ⟨(-654951823638257784), (-654262428350279128)⟩, true⟩

def words03 : List Nat := [371285110127451364, 371285109811603521, 371285109612842022, 371285109614210464, 371285109136164223, 371285108607584204, 371285108078445154, 371285108054293859, 371285108234479146, 371285108615149421]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473109698729279, 362473134272023432⟩, ⟨496762649860725796, 497452556741201988⟩, true⟩

def words04 : List Nat := [371285108932428213, 371285108933794262, 371285108602953582, 371285108728226980, 371285108882671602, 371285108884037737, 371285108267015239, 371285107537199250, 371285106806864115, 371285106656060525]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362461027413574169, 362461051999192800⟩, ⟨998935962718839659, 999626381744434677⟩, true⟩

def words05 : List Nat := [371285106535570564, 371285106703808884, 371285106854733594, 371285106856100107, 371285106316321509, 371285105951819322, 371285105643616388, 371285105644992065, 371285105184241781, 371285104607030732]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472593552587000, 362472618150437768⟩, ⟨518237619959353445, 518928547415989989⟩, true⟩

def words06 : List Nat := [371285104029233634, 371285103689958863, 371285103061969171, 371285102946557841, 371285102830742075, 371285102548250689, 371285101784007886, 371285101556110697, 371285101395292296, 371285101396707097]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473177701831600, 362473202312153956⟩, ⟨493960172995328253, 494651618955692767⟩, true⟩

def words07 : List Nat := [371285101097452017, 371285100782256566, 371285100466546092, 371285100391660762, 371285100119992825, 371285100027985479, 371285099935509351, 371285099843024737, 371285098979866861, 371285098695486224]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362455597483925710, 362455622106408498⟩, ⟨1225110104851054938, 1225802056505424816⟩, true⟩

def words08 : List Nat := [371285098593970552, 371285098595341403, 371285098188038344, 371285097763320519, 371285097338080224, 371285097087821891, 371285096604348924, 371285096265629104, 371285095926485372, 371285095586968860]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489765637774416, 362489790272636090⟩, ⟨(-196126024783075782), (-195433558229072948)⟩, true⟩

def words09 : List Nat := [371285094879254739, 371285094376719650, 371285093946959163, 371285093948350429, 371285093542197569, 371285092999025825, 371285092488265947, 371285092489786576, 371285092348998008, 371285092463491381]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk415
