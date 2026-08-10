import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk554A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk554B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk554A

def state06 : KState := ⟨⟨360641898422299551, 360641917881406100⟩, ⟨(-3331257209806029919), (-3330528056370281687)⟩, true⟩

def words05 : List Nat := [360581860337758437, 360581860656165809, 360581861128071435, 360581861751844477, 360581862098220568, 360581862444644353, 360581863115198533, 360581864001326949, 360581865084783556, 360581866168375858]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360637573920160863, 360637593386621271⟩, ⟨(-3091557887108106287), (-3090828325790561731)⟩, true⟩

def words06 : List Nat := [360581866994368148, 360581867772946826, 360581868739075783, 360581869705395948, 360581870589851294, 360581871150571791, 360581871547670295, 360581871944845947, 360581872665968183, 360581873671350399]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360570789553046815, 360570809026774606⟩, ⟨613310909190222347, 614040873665542257⟩, true⟩

def words07 : List Nat := [360581874606762231, 360581875542283524, 360581876203132733, 360581876540278518, 360581876651411537, 360581876762742260, 360581877049519910, 360581877050291784, 360581877013386512, 360581876814692154]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605540879580086, 360605560360605029⟩, ⟨(-1314793479489425527), (-1314063110131939501)⟩, true⟩

def words08 : List Nat := [360581876678838644, 360581876992583063, 360581877570600419, 360581878148753667, 360581878441198150, 360581878441970113, 360581878702553530, 360581878995321398, 360581879280149000, 360581879707703984]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575188914403682, 360575208402779411⟩, ⟨369667482426331836, 370398259715201798⟩, true⟩

def words09 : List Nat := [360581879943214834, 360581880178801333, 360581880673992504, 360581881332533390, 360581881776914815, 360581882221415263, 360581882454482836, 360581882455255013, 360581882364666324, 360581882245296803]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk554B
