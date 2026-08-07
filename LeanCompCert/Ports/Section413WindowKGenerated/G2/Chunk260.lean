import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk260

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360623682851490662, 360623686867346358⟩, ⟨(-1054016206764284263), (-1053945577219695421)⟩, true⟩

def state01 : KState := ⟨⟨360578535937479850, 360578539956581662⟩, ⟨119711946147081385, 119782660106678443⟩, true⟩

def words00 : List Nat := [360583152832227244, 360583152832568045, 360583152908834162, 360583153685261161, 360583153685551503, 360583153446396106, 360583151733491308, 360583149272403116, 360583146811439446, 360583145210718790]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360453146744150068, 360453150766467306⟩, ⟨3381795020713919290, 3381865818322812528⟩, true⟩

def words01 : List Nat := [360583145037933211, 360583145042267625, 360583145042573607, 360583143850559476, 360583141185531874, 360583137406072088, 360583133626803456, 360583131322403942, 360583127545326713, 360583122550415147]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602544742430051, 360602548767967512⟩, ⟨(-506332684567779481), (-506261803153085693)⟩, true⟩

def words02 : List Nat := [360583117555810755, 360583114035863528, 360583111258057265, 360583109471137120, 360583107684328151, 360583104602177875, 360583102623290824, 360583101124900566, 360583099626522301, 360583100348653883]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360538257947614553, 360538261976404491⟩, ⟨1167402080974159034, 1167473047066916568⟩, true⟩

def words03 : List Nat := [360583100349705275, 360583100350793692, 360583100351074549, 360583101008358043, 360583101008643931, 360583100945899749, 360583100883127638, 360583099670455376, 360583097532177244, 360583095810777261]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360528575359287180, 360528579391289471⟩, ⟨1419674821159336023, 1419745870918257771⟩, true⟩

def words04 : List Nat := [360583094089390161, 360583093839921922, 360583092847090613, 360583091109283885, 360583089371554298, 360583087254964888, 360583085897865076, 360583084293379891, 360583082688979075, 360583080192476353]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360603610334510721, 360603614369734253⟩, ⟨(-535246683291292320), (-535175549603143958)⟩, true⟩

def words05 : List Nat := [360583078100671729, 360583077116154053, 360583076617135435, 360583077158173585, 360583077158491571, 360583076455846750, 360583076048762019, 360583077297472456, 360583078085819823, 360583078874181391]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360557678657816699, 360557682696298820⟩, ⟨661569331824800290, 661640550447541328⟩, true⟩

def words06 : List Nat := [360583078874491850, 360583078330246811, 360583076800714573, 360583076273956615, 360583075747147039, 360583074409002000, 360583071604145037, 360583068056219337, 360583064508494146, 360583062080665815]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360502446869299399, 360502450910996623⟩, ⟨2101682445379529369, 2101753747836166171⟩, true⟩

def words07 : List Nat := [360583061107471019, 360583060486595911, 360583059865734057, 360583058515239527, 360583055698822692, 360583051795567981, 360583047892512798, 360583045065804363, 360583042718144636, 360583039628321630]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360528002705126991, 360528006750055069⟩, ⟨1435211109061168393, 1435282495794173961⟩, true⟩

def words08 : List Nat := [360583036538660415, 360583033663690848, 360583031992429861, 360583031787763300, 360583031583086149, 360583029972536347, 360583026896998514, 360583024442805271, 360583021988705231, 360583019494240358]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360503975927615953, 360503979975803744⟩, ⟨2062155528833628676, 2062227000628616958⟩, true⟩

def words09 : List Nat := [360583017386054321, 360583014269203610, 360583011152524431, 360583009021877681, 360583007628487961, 360583005340089618, 360583003051823688, 360583000023405541, 360582995531585423, 360582992504563462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk260
