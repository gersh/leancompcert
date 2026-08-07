import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk543

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360561766319838549, 360561784941555730⟩, ⟨1086518199339812884, 1087201395034206872⟩, true⟩

def state01 : KState := ⟨⟨360553954733402882, 360553973362222526⟩, ⟨1510702389319517140, 1511385970713817220⟩, true⟩

def words00 : List Nat := [360581806698582480, 360581806432055436, 360581806024487515, 360581805399606997, 360581804774626518, 360581804064624594, 360581803619550016, 360581803225610788, 360581802831604054, 360581802232977706]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591025689763750, 360591044325715332⟩, ⟨(-502875464355943118), (-502191495591293666)⟩, true⟩

def words01 : List Nat := [360581801721189336, 360581801547843984, 360581801374293785, 360581801193152477, 360581800914515222, 360581800303848685, 360581799693060374, 360581799265022310, 360581799267932720, 360581799438920331]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569421768669597, 360569440411804927⟩, ⟨670657396952594708, 671341755973956620⟩, true⟩

def words02 : List Nat := [360581799439594010, 360581799400907555, 360581799159808554, 360581799208829242, 360581799209461966, 360581799070444985, 360581798777970752, 360581798222556018, 360581797667021423, 360581797153126002]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563189070456328, 360563207720698580⟩, ⟨1009423971242118831, 1010108716418348187⟩, true⟩

def words03 : List Nat := [360581797036844832, 360581797148140806, 360581797148819462, 360581797089747265, 360581797039612098, 360581796904596939, 360581796870536866, 360581796871291743, 360581796739145474, 360581796397850188]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578201607321899, 360578220264694046⟩, ⟨193574585800604922, 194259718451312326⟩, true⟩

def words04 : List Nat := [360581796056396711, 360581795704299978, 360581795544189153, 360581795567458156, 360581795568154278, 360581795303352829, 360581794861593306, 360581794757850611, 360581794653878602, 360581794500544117]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360538632786546814, 360538651451111134⟩, ⟨2344323576446076941, 2345009100026668495⟩, true⟩

def words05 : List Nat := [360581794435466274, 360581794090964611, 360581793746334025, 360581793372947948, 360581793169414688, 360581792733148104, 360581792296815166, 360581791691395266, 360581790748242926, 360581789955526636]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574456287259566, 360574474958945312⟩, ⟨396845017715875555, 397530928452396983⟩, true⟩

def words06 : List Nat := [360581789162581125, 360581788707441211, 360581788437200526, 360581787997941001, 360581787558574627, 360581786983972661, 360581786724960688, 360581786764684889, 360581786765375769, 360581786544901766]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598101175258500, 360598119854074502⟩, ⟨(-888846743407046038), (-888160444964050112)⟩, true⟩

def words07 : List Nat := [360581786614080868, 360581786817950985, 360581787072388004, 360581787129554310, 360581787130252217, 360581786892032911, 360581786752136208, 360581787068976150, 360581787369935462, 360581787671051681]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565795377839965, 360565814063856315⟩, ⟨867877457958496900, 868564147991209146⟩, true⟩

def words08 : List Nat := [360581787803075026, 360581787803830450, 360581787598501497, 360581787247556920, 360581786896419713, 360581786401265274, 360581785675802205, 360581784780386174, 360581783884858478, 360581783252089285]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360508622052878560, 360508640746009239⟩, ⟨3977928232736904765, 3978615309754472019⟩, true⟩

def words09 : List Nat := [360581782959100407, 360581782938624628, 360581782918063621, 360581782728699922, 360581782202076246, 360581781366537832, 360581780530812921, 360581779575506917, 360581778400507278, 360581777056850314]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk543
