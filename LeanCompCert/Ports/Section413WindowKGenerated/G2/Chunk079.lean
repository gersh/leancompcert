import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk079

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360273565150327781, 360273565481738596⟩, ⟨2434464423616110656, 2434466198890986154⟩, true⟩

def state01 : KState := ⟨⟨360513266852266719, 360513267184560466⟩, ⟨539621246803162128, 539623029057584758⟩, true⟩

def words00 : List Nat := [360581686757461768, 360581663676278245, 360581648857083819, 360581633553422543, 360581618253625520, 360581588032597887, 360581550467858306, 360581528798239334, 360581507134073669, 360581487542216293]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360505104283779761, 360505104616964907⟩, ⟨604055550261214535, 604057339571067765⟩, true⟩

def words01 : List Nat := [360581478918819458, 360581462263941952, 360581445613256126, 360581437183624957, 360581436819325910, 360581432319573160, 360581427820948781, 360581409580008129, 360581384114213984, 360581374483072366]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360661389436404112, 360661389770471311⟩, ⟨(-634804744843784923), (-634802948543577917)⟩, true⟩

def words02 : List Nat := [360581367908266658, 360581367908360607, 360581366745209860, 360581355792704773, 360581344842947111, 360581329394559592, 360581330317014869, 360581338678686576, 360581338957190605, 360581349050695296]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360730821452843898, 360730821787797739⟩, ⟨(-1186623123049353262), (-1186621319713678786)⟩, true⟩

def words03 : List Nat := [360581349646067106, 360581350241314165, 360581366622798340, 360581367284008161, 360581367284094694, 360581353130371718, 360581340608020243, 360581354434089464, 360581373258769474, 360581392078729149]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360730074212778590, 360730074548626000⟩, ⟨(-1181702075756663828), (-1181700265321574552)⟩, true⟩

def words04 : List Nat := [360581402826646613, 360581416910323032, 360581432499941178, 360581448085661672, 360581452064616417, 360581452064710461, 360581449378925743, 360581438676181117, 360581433005711361, 360581451700516131]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360569855147901148, 360569855484635744⟩, ⟨93471468935280297, 93473286427912117⟩, true⟩

def words05 : List Nat := [360581486113709885, 360581520518268882, 360581542807944731, 360581558737246155, 360581565453221076, 360581572167534043, 360581589004085710, 360581599835053457, 360581599835138696, 360581598359815130]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360832538475466362, 360832538813089715⟩, ⟨(-1998612320364671986), (-1998610495793019928)⟩, true⟩

def words06 : List Nat := [360581601464112081, 360581613943034883, 360581642099357170, 360581670248627905, 360581684005751559, 360581698725714103, 360581721831639202, 360581744931792480, 360581772125941693, 360581803585917087]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360553265476279079, 360553265814801357⟩, ⟨228468896344195426, 228470728084688932⟩, true⟩

def words07 : List Nat := [360581827010974876, 360581850430166906, 360581865251695780, 360581888159818843, 360581898958432299, 360581909754352942, 360581912542021363, 360581912542115722, 360581899819966607, 360581896231854577]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577524788346873, 360577525127757843⟩, ⟨34516944776240828, 34518783612998816⟩, true⟩

def words08 : List Nat := [360581895349918795, 360581895350013621, 360581894326854079, 360581885413709466, 360581876502782075, 360581863508801336, 360581862366853360, 360581859359298461, 360581856352486199, 360581845376019796]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360812137370808983, 360812137711112498⟩, ⟨(-1841124796289099623), (-1841122950316465073)⟩, true⟩

def words09 : List Nat := [360581853484329685, 360581862131142972, 360581886315047298, 360581911397821926, 360581922229348989, 360581933058174291, 360581945889097242, 360581968571005543, 360581997342224935, 360582026106273545]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk079
