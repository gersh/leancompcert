import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk768

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576648235376460, 360576686530369323⟩, ⟨419036292786034962, 421022707578196270⟩, true⟩

def state01 : KState := ⟨⟨360594073848016858, 360594112153323000⟩, ⟨(-919325110320599857), (-917337903415773519)⟩, true⟩

def words00 : List Nat := [360582168624254298, 360582168698340164, 360582168699316170, 360582168688663610, 360582168677808464, 360582168693116716, 360582168891326600, 360582169089740960, 360582169203309887, 360582169359928620]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595602106023030, 360595640421684123⟩, ⟨(-1036806520342718469), (-1034818518024189679)⟩, true⟩

def words01 : List Nat := [360582169512394248, 360582169665162520, 360582169844409384, 360582169887011794, 360582169888032634, 360582169782582183, 360582169676930971, 360582169552845567, 360582169729087579, 360582169905574932]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581427575327601, 360581465901419799⟩, ⟨52017654910114502, 54006458597307600⟩, true⟩

def words02 : List Nat := [360582169977520203, 360582169978615913, 360582169945803335, 360582169959006608, 360582169959940695, 360582169855683290, 360582169621887328, 360582169303538770, 360582168984988754, 360582168835932325]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564799659548049, 360564837995968639⟩, ⟨1329696937540453404, 1331686534809590160⟩, true⟩

def words03 : List Nat := [360582168987631263, 360582169148704364, 360582169224083305, 360582169225179463, 360582169202474638, 360582169064267911, 360582168955420199, 360582168956515987, 360582168862422018, 360582168638014574]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594838034084372, 360594876380850647⟩, ⟨(-978623711761066502), (-976633319479647150)⟩, true⟩

def words04 : List Nat := [360582168413361856, 360582168298254885, 360582168271317234, 360582168219765241, 360582168168129974, 360582167975214390, 360582167933607308, 360582167998092782, 360582168073669538, 360582168240169594]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360576905408376346, 360576943765607349⟩, ⟨399578645130281866, 401569841676047322⟩, true⟩

def words05 : List Nat := [360582168321034000, 360582168402006566, 360582168478862036, 360582168640812138, 360582168720957930, 360582168801283597, 360582168802269624, 360582168727837141, 360582168524490152, 360582168457796733]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564762264262963, 360564800631809631⟩, ⟨1332961662382024041, 1334953651842319939⟩, true⟩

def words06 : List Nat := [360582168449956179, 360582168451052412, 360582168342428010, 360582168149321822, 360582167956042001, 360582167720647008, 360582167596558950, 360582167438112132, 360582167279557602, 360582167012085972]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599535965864357, 360599574343757564⟩, ⟨(-1340207562212964178), (-1338214777363495624)⟩, true⟩

def words07 : List Nat := [360582166787056522, 360582166731291755, 360582166787169503, 360582167006439321, 360582167070268041, 360582167134178573, 360582167312558238, 360582167575545666, 360582167802853715, 360582168030398432]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600197144999233, 360600235533347339⟩, ⟨(-1391137219960849454), (-1389143631287345460)⟩, true⟩

def words08 : List Nat := [360582168126329107, 360582168172071868, 360582168386491047, 360582168601226884, 360582168773283996, 360582168848495763, 360582168849481955, 360582168839331559, 360582168896228014, 360582169132451430]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562980228817699, 360563018627483684⟩, ⟨1470688967874925676, 1472683349942498270⟩, true⟩

def words09 : List Nat := [360582169425965352, 360582169719679596, 360582169901510660, 360582169914760138, 360582169915698402, 360582169789217127, 360582169666568926, 360582169667665534, 360582169504121174, 360582169256221558]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk768
