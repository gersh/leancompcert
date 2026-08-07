import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk008

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362855582043153598, 362855582049283761⟩, ⟨(-323947130716803430), (-323947127374944906)⟩, true⟩

def state01 : KState := ⟨⟨361569555178141228, 361569555184436557⟩, ⟨705291932391245855, 705291935866099407⟩, true⟩

def words00 : List Nat := [371251620697164278, 371251620697182451, 371250067672525906, 371249244788419777, 371248423948738030, 371247507984311091, 371245334111014671, 371243150701468068, 371240972689712821, 371240285969456433]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361092972446770675, 361092972453233282⟩, ⟨1101544127819080684, 1101544131430292056⟩, true⟩

def words01 : List Nat := [371239623655503226, 371240033980441724, 371240434140757550, 371240434140776195, 371239644269637912, 371239246376017272, 371239373592162264, 371239373592180885, 371237959182675770, 371236318954977541]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨363232056660186136, 363232056666816878⟩, ⟨(-660507607269240832), (-660507603519277900)⟩, true⟩

def words02 : List Nat := [371234682722954136, 371234491255866002, 371234110822858410, 371234640003889754, 371234725067241699, 371234725067260796, 371234065705681254, 371234451776154352, 371236264373400665, 371237222005542176]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362807862166658369, 362807862173462883⟩, ⟨(-306541073395102327), (-306541069500026649)⟩, true⟩

def words03 : List Nat := [371238169955850689, 371239115630174572, 371240317803657508, 371240816014750540, 371241691199014582, 371242564292044930, 371243457717355359, 371243457717374456, 371242932328796129, 371243366252535385]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361449951724026715, 361449951731002178⟩, ⟨842885075085554217, 842885079125126331⟩, true⟩

def words04 : List Nat := [371244861656780602, 371244861656799740, 371244517160017860, 371244172552773798, 371243828761161272, 371243753649310644, 371243080717174583, 371242575154030209, 371242070781840820, 371241581235855268]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨364212447975297219, 364212447982447550⟩, ⟨(-1521065634978725611), (-1521065630789602449)⟩, true⟩

def words05 : List Nat := [371240415983806382, 371240005202038148, 371240527464106313, 371240527464125939, 371240411010298104, 371240154384250087, 371240976392118550, 371241708016417631, 371243767016391478, 371245821233562995]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362505067183352439, 362505067190680704⟩, ⟨(-47014025515196019), (-47014021172125487)⟩, true⟩

def words06 : List Nat := [371247493320045957, 371247493320065587, 371248640296869012, 371249870950212292, 371251471532212915, 371251471532232609, 371251329473295892, 371251025635940729, 371251028085862680, 371251090128485382]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361788569744516764, 361788569752025218⟩, ⟨583484260226735165, 583484264727498659⟩, true⟩

def words07 : List Nat := [371251892318607388, 371252692670959380, 371253376924860090, 371253376924880130, 371252952983628123, 371252594499448044, 371253151733546450, 371253151733566534, 371252374376265747, 371251620052851922]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362717723088613068, 362717723096302415⟩, ⟨(-232448338586862626), (-232448333925975234)⟩, true⟩

def words08 : List Nat := [371251375568807972, 371251414443074481, 371252709468654343, 371254001567630766, 371255001557150242, 371255001557170495, 371254919366971099, 371255501542414704, 371256545192993818, 371256838321974722]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362122243319761191, 362122243327636893⟩, ⟨302243198045460627, 302243202873158719⟩, true⟩

def words09 : List Nat := [371256890222112278, 371256942006018546, 371257774254916257, 371257991138983945, 371258560215098564, 371259128022378484, 371259594640264593, 371259594640285158, 371258442663399368, 371258069108607070]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk008
