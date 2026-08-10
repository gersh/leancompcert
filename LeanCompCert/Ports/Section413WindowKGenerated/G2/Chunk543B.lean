import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk543A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk543B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk543A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk543B
