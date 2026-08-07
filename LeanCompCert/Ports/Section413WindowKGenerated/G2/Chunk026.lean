import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk026

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360519321535285247, 360519321567058281⟩, ⟨116864163761881535, 116864219930075475⟩, true⟩

def state01 : KState := ⟨⟨359933153648367707, 359933153680400975⟩, ⟨1639699168142463871, 1639699224988555957⟩, true⟩

def words00 : List Nat := [360564252063019038, 360564132479697345, 360563869284482109, 360563654502957434, 360563439886324655, 360563184990015185, 360562786800281732, 360562273197837509, 360561759989104071, 360561390931354445]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨359604448735013193, 359604448767305431⟩, ⟨2497536374684548366, 2497536432207870006⟩, true⟩

def words01 : List Nat := [360561150319637879, 360560900913993896, 360560651699243064, 360560299874073375, 360559805481586147, 360559271749940005, 360558738426181827, 360558348388250720, 360558070925431959, 360557706947537443]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360289513256195268, 360289513288747638⟩, ⟨700926635060015607, 700926693266158993⟩, true⟩

def words02 : List Nat := [360557343247376552, 360557122378469677, 360557004320669503, 360556947962388793, 360556891647045915, 360556698165163095, 360556485263302535, 360556327602427194, 360556170061483651, 360556025339419182]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨359614982949804023, 359614982982620086⟩, ⟨2480882263059314062, 2480882321960325640⟩, true⟩

def words03 : List Nat := [360555924042579196, 360555749496686426, 360555575083371266, 360555582782385969, 360555582782409229, 360555525016524592, 360555467294448918, 360555337331379412, 360555067227363092, 360554711134877786]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨359595212353586096, 359595212386663703⟩, ⟨2531234280874749791, 2531234340467569137⟩, true⟩

def words04 : List Nat := [360554355312048309, 360554048564005853, 360553602016074652, 360553083094823162, 360552564565946214, 360551972825984424, 360551491292421078, 360551149702913383, 360550808371303351, 360550395156651465]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359825415347617246, 359825415380958301⟩, ⟨1916988917263277856, 1916988977555537278⟩, true⟩

def words05 : List Nat := [360550034846312080, 360549688437535834, 360549342289896770, 360548988000980910, 360548494995615282, 360547872928334323, 360547251329295971, 360546768566092611, 360546358960302964, 360546087928911511]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨359678033836366659, 359678033869974132⟩, ⟨2308298728692623465, 2308298789694889395⟩, true⟩

def words06 : List Nat := [360545817101222000, 360545475482538016, 360545111589121812, 360544885846947524, 360544660274178374, 360544336999310734, 360543968969873920, 360543489627212898, 360543010643739311, 360542565251882331]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359745205299415076, 359745205333287229⟩, ⟨2129970782394219618, 2129970844104521654⟩, true⟩

def words07 : List Nat := [360542241578606029, 360542055355554714, 360541869271837064, 360541577590249979, 360541299643589439, 360540978258911470, 360540657114333565, 360540472907667656, 360540267238485619, 360539970573624738]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360754927581899074, 360754927616037906⟩, ⟨(-582561334534792894), (-582561272108434668)⟩, true⟩

def words08 : List Nat := [360539674130067092, 360539369430668410, 360539141867049599, 360539050646068189, 360538959493032943, 360538750529697144, 360538517324435730, 360538420227913684, 360538362087343828, 360538442565087169]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360732896809707103, 360732896844115652⟩, ⟨(-524063337204665623), (-524063274051430245)⟩, true⟩

def words09 : List Nat := [360538442565112710, 360538421691392161, 360538515525642067, 360538700656878813, 360538760324274893, 360538819947427831, 360538819947453094, 360538790659487477, 360538799335175211, 360538871196558662]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk026
