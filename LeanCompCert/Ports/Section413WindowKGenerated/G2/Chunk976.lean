import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk976

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585883562989015, 360585946572917562⟩, ⟨(-349156814310445901), (-345004264176668509)⟩, true⟩

def state01 : KState := ⟨⟨360596984842800396, 360597047866124441⟩, ⟨(-1432776808765005939), (-1428622951165346081)⟩, true⟩

def words00 : List Nat := [360582411743412298, 360582411810073375, 360582411852363265, 360582411894920490, 360582411896241222, 360582411848821321, 360582411740375562, 360582411737293940, 360582411834012503, 360582411985422826]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590174512568174, 360590237549388150⟩, ⟨(-767941497542241651), (-763786322539755355)⟩, true⟩

def words01 : List Nat := [360582412084007800, 360582412182747569, 360582412386119050, 360582412691751301, 360582412925410779, 360582413159276084, 360582413326981622, 360582413390234714, 360582413471531058, 360582413553295714]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599576150879629, 360599639201065554⟩, ⟨(-1685772207917213850), (-1681615728063983328)⟩, true⟩

def words02 : List Nat := [360582413697406848, 360582413879122768, 360582414008116150, 360582414137249795, 360582414190171381, 360582414304634206, 360582414504801614, 360582414705236717, 360582414824623512, 360582415002521404]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360613121380603208, 360613184444165092⟩, ⟨(-3008307973562845152), (-3004150187747239680)⟩, true⟩

def words03 : List Nat := [360582415215842093, 360582415429587984, 360582415723941525, 360582415913982984, 360582416008350157, 360582416102858430, 360582416279506928, 360582416508780944, 360582416825043108, 360582417141620595]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585085606286175, 360585148683389850⟩, ⟨(-270888380476315501), (-266729272378976065)⟩, true⟩

def words04 : List Nat := [360582417392619823, 360582417539192349, 360582417604748181, 360582417670692204, 360582417687903356, 360582417689321412, 360582417602059828, 360582417433381037, 360582417264430025, 360582417228797691]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360575771903141170, 360575834993592605⟩, ⟨638674557172294025, 642834968745306179⟩, true⟩

def words05 : List Nat := [360582417362738050, 360582417496947519, 360582417568919443, 360582417570337611, 360582417561149450, 360582417525821162, 360582417490089991, 360582417450266941, 360582417436839584, 360582417370909268]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587915590717910, 360587978694551812⟩, ⟨(-547283361948942052), (-543121643377090422)⟩, true⟩

def words06 : List Nat := [360582417312017905, 360582417387739155, 360582417546709534, 360582417705973374, 360582417763254996, 360582417764673781, 360582417813749543, 360582417878487776, 360582417910413440, 360582417968815646]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589382268949302, 360589445386303903⟩, ⟨(-690539990262726010), (-686376951057079950)⟩, true⟩

def words07 : List Nat := [360582417970101340, 360582417947643668, 360582418005810013, 360582418150833744, 360582418268814988, 360582418387023916, 360582418452589506, 360582418520523505, 360582418593610529, 360582418667176775]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593118133307529, 360593181264008786⟩, ⟨(-1055501220872001720), (-1051336877897648880)⟩, true⟩

def words08 : List Nat := [360582418746514464, 360582418841706994, 360582418884182614, 360582418926812247, 360582418928020154, 360582418931243757, 360582419068964515, 360582419206954418, 360582419292247364, 360582419403879423]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592141723262586, 360592204867376102⟩, ⟨(-960125685761960245), (-955960032479068167)⟩, true⟩

def words09 : List Nat := [360582419507848810, 360582419612252073, 360582419804633039, 360582419892832302, 360582419894159381, 360582419891612173, 360582419970061997, 360582420117373823, 360582420218694899, 360582420320314362]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk976
