import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk554

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360615662891347755, 360615682306666872⟩, ⟨(-1875331066707990004), (-1874604340406020908)⟩, true⟩

def state01 : KState := ⟨⟨360587916512778897, 360587935935437987⟩, ⟨(-338221721844316970), (-337494588871966394)⟩, true⟩

def words00 : List Nat := [360581845705383757, 360581845792237926, 360581845987731074, 360581846183452154, 360581846184108524, 360581846156166430, 360581846033779459, 360581845637999916, 360581845242087137, 360581845184704885]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574794719242712, 360574814149172662⟩, ⟨388997605340809211, 389725141227509215⟩, true⟩

def words01 : List Nat := [360581845620121779, 360581846055684018, 360581846294391943, 360581846301480189, 360581846302125514, 360581846227402162, 360581846331298883, 360581846485698286, 360581846486401311, 360581846360309933]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360620830596617967, 360620850033823389⟩, ⟨(-2162531607773212162), (-2161803668643750410)⟩, true⟩

def words02 : List Nat := [360581846360633342, 360581846651927628, 360581847087596868, 360581847523396771, 360581847681752426, 360581847950692697, 360581848425598045, 360581848900712907, 360581849425615636, 360581850130003438]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609109594548022, 360609129039117295⟩, ⟨(-1512817681516822290), (-1512089334173125078)⟩, true⟩

def words03 : List Nat := [360581850668212776, 360581851206483869, 360581851736716404, 360581852430304163, 360581853041982943, 360581853653765525, 360581854038708297, 360581854206974752, 360581854699568664, 360581855192430311]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599780468096128, 360599799919919706⟩, ⟨(-995514164316737758), (-994785414757042210)⟩, true⟩

def words04 : List Nat := [360581856009458478, 360581856688533857, 360581857205341619, 360581857722215074, 360581858055711039, 360581858552380342, 360581859003071269, 360581859453883491, 360581859695229242, 360581860019561606]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk554
