import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk252

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502475780194184, 362502484451861831⟩, ⟨(-420737036073863443), (-420589291069606345)⟩, true⟩

def state01 : KState := ⟨⟨362436759200564530, 362436767879313780⟩, ⟨1235662157930863465, 1235810081429349277⟩, true⟩

def words00 : List Nat := [371285796175214922, 371285796176011137, 371285795191963662, 371285794229697463, 371285793267211205, 371285792710536702, 371285791371425077, 371285790412280170, 371285789452940995, 371285788509279245]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502490260550463, 362502498946496997⟩, ⟨(-421790561021003847), (-421642456042126507)⟩, true⟩

def words01 : List Nat := [371285786565407472, 371285785599723212, 371285784817243931, 371285784818054301, 371285783700994036, 371285782229076452, 371285780756941591, 371285780615148138, 371285780370822439, 371285781034596513]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362453773354733405, 362453782047872339⟩, ⟨806874802312125710, 807023088720510386⟩, true⟩

def words02 : List Nat := [371285781397625097, 371285781398421979, 371285779668338401, 371285778737254427, 371285777805845756, 371285777332897425, 371285774767509479, 371285772219879378, 371285769672118143, 371285768694274262]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362441788087724342, 362441796788045736⟩, ⟨1109496175750719001, 1109644643409206777⟩, true⟩

def words03 : List Nat := [371285767427064546, 371285767289455090, 371285767151579045, 371285767014578047, 371285765839689746, 371285764684047516, 371285763940046328, 371285763940843614, 371285762262931470, 371285760521936751]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476298444158999, 362476307151630179⟩, ⟨238458795225855815, 238607443381284357⟩, true⟩

def words04 : List Nat := [371285758780719745, 371285758286373349, 371285757725571610, 371285758229551979, 371285758230181597, 371285758093257009, 371285756470597046, 371285756415777193, 371285756950541596, 371285756951368052]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481671656236849, 362481680370966464⟩, ⟨102893382317620673, 103042213785155715⟩, true⟩

def words05 : List Nat := [371285756577731464, 371285756177411492, 371285756942339975, 371285757493602077, 371285758521267937, 371285759549185167, 371285760568617590, 371285760569415519, 371285759795689567, 371285759635170152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468173837068338, 362468182558913082⟩, ⟨443984112382427449, 444133123615790017⟩, true⟩

def words06 : List Nat := [371285760878529661, 371285760879329830, 371285760698700542, 371285760179771984, 371285759660570051, 371285759487426337, 371285758536529474, 371285758383223880, 371285758229669140, 371285758068355733]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494841938633078, 362494850667703571⟩, ⟨(-229983349669088461), (-229834155805707085)⟩, true⟩

def words07 : List Nat := [371285757907552188, 371285758442620766, 371285760393342296, 371285760394140600, 371285760260292028, 371285759851370058, 371285759442174039, 371285759379149594, 371285759125822272, 371285759486349760]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362444245362100070, 362444254098378457⟩, ⟨1049297921118741373, 1049447297234225869⟩, true⟩

def words08 : List Nat := [371285759820652337, 371285759821450928, 371285758072502020, 371285757728077836, 371285757383282124, 371285757329113444, 371285755524139777, 371285753712453951, 371285751900584684, 371285750630495271]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362425884981588224, 362425893725065645⟩, ⟨1513747750378123038, 1513897308593093118⟩, true⟩

def words09 : List Nat := [371285748990284398, 371285747994403025, 371285746998338972, 371285745995724683, 371285742911977486, 371285740304601764, 371285737697006257, 371285736261340962, 371285733927677863, 371285731563349957]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk252
