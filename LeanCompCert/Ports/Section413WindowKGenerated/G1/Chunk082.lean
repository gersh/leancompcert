import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk082

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362307994595530082, 362307995426127064⟩, ⟨1438954377026962034, 1438958989093645964⟩, true⟩

def state01 : KState := ⟨⟨362424960663446989, 362424961496156973⟩, ⟨479436469866574437, 479441099270628515⟩, true⟩

def words00 : List Nat := [371283456832103136, 371283447057696616, 371283429844829416, 371283422325077500, 371283414807083663, 371283404515734101, 371283381143414250, 371283368752074848, 371283358706542547, 371283358706786770]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362453411702814463, 362453412537675898⟩, ⟨245564516137291580, 245569163215807406⟩, true⟩

def words01 : List Nat := [371283351594896874, 371283340084433836, 371283328958276430, 371283328958536583, 371283322340377723, 371283318810884451, 371283315282170903, 371283309102997605, 371283290766272951, 371283287131741082]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362365874492551419, 362365875329519973⟩, ⟨965842493578555974, 965847157988602118⟩, true⟩

def words02 : List Nat := [371283294558964724, 371283294559201255, 371283285994739266, 371283277527207140, 371283269061644173, 371283261139576229, 371283246000180267, 371283241532509121, 371283237065845377, 371283232213844226]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362527795672528977, 362527796511641602⟩, ⟨(-367080795890439737), (-367076113824004091)⟩, true⟩

def words03 : List Nat := [371283218359596590, 371283218763292324, 371283233821178983, 371283233821416061, 371283233558038517, 371283230447310974, 371283238873815136, 371283243032166343, 371283248439307006, 371283253845238981]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362536066989201348, 362536067830453610⟩, ⟨(-435723552027444716), (-435718852319458768)⟩, true⟩

def words04 : List Nat := [371283256900892469, 371283256901130578, 371283250098880401, 371283254017159191, 371283257869401097, 371283257869642939, 371283253504992483, 371283249208645937, 371283253423839719, 371283259825082206]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362379406846828369, 362379407690217468⟩, ⟨857953595325868820, 857958312673686042⟩, true⟩

def words05 : List Nat := [371283276621171742, 371283293413284344, 371283307350001777, 371283307350239151, 371283301806284929, 371283298501883548, 371283301984447874, 371283301984685350, 371283289311534385, 371283276735335348]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362432137425045449, 362432138270560836⟩, ⟨422435509081266583, 422440244003191459⟩, true⟩

def words06 : List Nat := [371283264162075395, 371283259011737062, 371283251175907727, 371283254533951153, 371283256476086830, 371283256476324582, 371283239000560025, 371283227594453521, 371283219315538816, 371283219315784923]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362454772624645244, 362454773472333147⟩, ⟨235503039878555870, 235507792777990322⟩, true⟩

def words07 : List Nat := [371283213140043400, 371283206784012448, 371283208593073639, 371283211615641942, 371283218623386598, 371283225629525971, 371283232437090215, 371283232437328408, 371283219877732647, 371283216442475417]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362343732466268685, 362343733316082555⟩, ⟨1155344570689786995, 1155349341203285501⟩, true⟩

def words08 : List Nat := [371283213218230803, 371283213218469170, 371283197145995157, 371283178011617692, 371283158881770540, 371283144263301228, 371283122358673030, 371283114929663356, 371283107502360545, 371283099943489466]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362659867452932342, 362659868304900297⟩, ⟨(-1466787813249592247), (-1466783024867758929)⟩, true⟩

def words09 : List Nat := [371283083134264845, 371283080790941603, 371283090563848227, 371283095615129481, 371283097805942478, 371283099996300775, 371283116630045259, 371283126163868451, 371283147458264921, 371283168747633973]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk082
