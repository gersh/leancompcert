import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk679

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470227810950592, 362470296070291553⟩, ⟨1026044798641718819, 1029175084679328561⟩, true⟩

def state01 : KState := ⟨⟨362475026582995345, 362475094863065408⟩, ⟨700239145102247630, 703370838754800164⟩, true⟩

def words00 : List Nat := [371285453066381633, 371285453062428580, 371285452949168536, 371285452948307984, 371285452946710628, 371285452911875156, 371285452652042072, 371285452462703312, 371285452272193659, 371285452260190350]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480112967757797, 362480181268998285⟩, ⟨354824260003774185, 357957391444648001⟩, true⟩

def words01 : List Nat := [371285452109410199, 371285451959547785, 371285451855155989, 371285451857799609, 371285451847955326, 371285451850908558, 371285451853220494, 371285451855542647, 371285451623303949, 371285451548613195]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362463355394662846, 362463423716576567⟩, ⟨1493067278549750184, 1496201814226325244⟩, true⟩

def words02 : List Nat := [371285451472621465, 371285451472516212, 371285451183014103, 371285450893642178, 371285450603435735, 371285450311374407, 371285449910057416, 371285449726301885, 371285449541703540, 371285449357887127]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490686436359218, 362490754779229212⟩, ⟨(-363666236143630945), (-360530276804650967)⟩, true⟩

def words03 : List Nat := [371285449035225562, 371285448930308333, 371285448932994688, 371285448935315140, 371285448757218834, 371285448528826751, 371285448299448154, 371285448237196822, 371285448178515213, 371285448259207360]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476494314417779, 362476562678260056⟩, ⟨600651461136808666, 603788845437653314⟩, true⟩

def words04 : List Nat := [371285448338479914, 371285448340844592, 371285448431946193, 371285448587732554, 371285448793393919, 371285448795715416, 371285448745831609, 371285448639891416, 371285448533063079, 371285448459649867]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474527960683224, 362474596345439176⟩, ⟨734305231345337649, 737444036839030875⟩, true⟩

def words05 : List Nat := [371285448342718541, 371285448357523557, 371285448371638462, 371285448373960086, 371285448128571326, 371285447950132040, 371285447805605453, 371285447807942544, 371285447650758275, 371285447493715207]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481794944604889, 362481863350184001⟩, ⟨240448922087954792, 243589142826385580⟩, true⟩

def words06 : List Nat := [371285447392306132, 371285447394864868, 371285447379741047, 371285447401077758, 371285447402876806, 371285447381035124, 371285447137167913, 371285447110883865, 371285447122092379, 371285447124537781]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486843721522830, 362486912148204319⟩, ⟨(-102730463611720122), (-99588808436985368)⟩, true⟩

def words07 : List Nat := [371285447073548459, 371285447015476782, 371285447084322435, 371285447106575340, 371285447194557983, 371285447283448329, 371285447342416704, 371285447344739885, 371285447173160314, 371285447197579336]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488103122915431, 362488171570284279⟩, ⟨(-188335663125555561), (-185192601517432303)⟩, true⟩

def words08 : List Nat := [371285447416022124, 371285447418349608, 371285447413185509, 371285447384050859, 371285447387956289, 371285447390541723, 371285447461865487, 371285447607336239, 371285447746695894, 371285447789173288]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502026102841414, 362502094571246549⟩, ⟨(-1135072954084396174), (-1131928462113998396)⟩, true⟩

def words09 : List Nat := [371285447854112167, 371285447920235086, 371285448201299964, 371285448203622895, 371285448196675539, 371285448155874689, 371285448252371145, 371285448315423077, 371285448561797018, 371285448809241373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk679
