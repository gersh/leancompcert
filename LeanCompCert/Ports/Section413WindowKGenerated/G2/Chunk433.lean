import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk433

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588928998970673, 360588940622696224⟩, ⟨(-251183631532382167), (-250843497390298153)⟩, true⟩

def state01 : KState := ⟨⟨360578107265986457, 360578118895295014⟩, ⟨217517078806691532, 217857454720521532⟩, true⟩

def words00 : List Nat := [360583147733408610, 360583148273714264, 360583148966532131, 360583149659428872, 360583149903327917, 360583149903918723, 360583149811278618, 360583149632121174, 360583149452801316, 360583149083582258]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604689765625892, 360604701400558891⟩, ⟨(-933956154880518781), (-933615535344164757)⟩, true⟩

def words01 : List Nat := [360583148967967381, 360583148583758789, 360583148347620242, 360583148763720978, 360583149041979684, 360583149320336735, 360583149331424466, 360583149332019321, 360583149794728256, 360583150292889536]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604475616988269, 360604487257492725⟩, ⟨(-924729908691091359), (-924389047771358189)⟩, true⟩

def words02 : List Nat := [360583151323591833, 360583151823420741, 360583151911760123, 360583152000150971, 360583152000646078, 360583152247819887, 360583152842248831, 360583153436763262, 360583153560868377, 360583154053833189]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360615542950583870, 360615554596663561⟩, ⟨(-1404303849616035246), (-1403962747094404734)⟩, true⟩

def words03 : List Nat := [360583155079147532, 360583156104588650, 360583157305986785, 360583158158990427, 360583158560232918, 360583158961497469, 360583159173081344, 360583159691507704, 360583160439446439, 360583161187487622]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612220488665162, 360612232140371366⟩, ⟨(-1260454015627719277), (-1260112669225534493)⟩, true⟩

def words04 : List Nat := [360583161667108000, 360583161990526564, 360583162711324941, 360583163432280796, 360583164015588836, 360583164068588404, 360583164069115097, 360583163853996743, 360583163796690708, 360583164467901861]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360564940570693262, 360564952227974218⟩, ⟨789275775911267776, 789617364006635134⟩, true⟩

def words05 : List Nat := [360583164853315420, 360583165238812932, 360583165357606631, 360583165358198174, 360583165128458775, 360583164437502088, 360583163746404090, 360583163457103990, 360583163379925590, 360583162960538947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598100760021976, 360598112422886577⟩, ⟨(-648635411207113802), (-648293580978092392)⟩, true⟩

def words06 : List Nat := [360583162541037780, 360583162906701777, 360583163684516539, 360583164462408981, 360583164715795856, 360583164716387484, 360583164439756788, 360583164339783393, 360583164449459425, 360583164794725408]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573550817826170, 360573562486334243⟩, ⟨416220604136364300, 416562679150464336⟩, true⟩

def words07 : List Nat := [360583164808412955, 360583164822169692, 360583164916577196, 360583165277623092, 360583165477367175, 360583165677197992, 360583165677726203, 360583165556468716, 360583165350614645, 360583165129929229]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562968242457467, 360562979916538031⟩, ⟨875233142293198495, 875575459070452163⟩, true⟩

def words08 : List Nat := [360583164909054254, 360583164653390025, 360583163985732923, 360583163050559167, 360583162115325972, 360583161043466983, 360583160379525346, 360583160047170009, 360583159714770714, 360583159115871298]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613069030092076, 360613080709767971⟩, ⟨(-1298979397743499089), (-1298636838156877381)⟩, true⟩

def words09 : List Nat := [360583158717033230, 360583158783420470, 360583158834799942, 360583158835394710, 360583158730284535, 360583158094140966, 360583157457912162, 360583157511398477, 360583158201351840, 360583158891419157]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk433
