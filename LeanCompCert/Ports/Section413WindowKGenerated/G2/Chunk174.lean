import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk174

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593675780543452, 360593677515833448⟩, ⟨(-169763238424013690), (-169742799221166222)⟩, true⟩

def state01 : KState := ⟨⟨360638398699414909, 360638400436786425⟩, ⟨(-947841475188297574), (-947820999756443380)⟩, true⟩

def words00 : List Nat := [360583926593569212, 360583932254331627, 360583936257181480, 360583940259595919, 360583942899429571, 360583947246740999, 360583952104892362, 360583956962527397, 360583959253344025, 360583962380399288]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360708068393343062, 360708070132797557⟩, ⟨(-2161506200604177084), (-2161485688897163312)⟩, true⟩

def words01 : List Nat := [360583966972426657, 360583971563990574, 360583976632385923, 360583978433168472, 360583978433374084, 360583977352472417, 360583978474035669, 360583982315126643, 360583989438601493, 360583996561309287]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360567134850508515, 360567136592069576⟩, ⟨293762286553646149, 293782834967260261⟩, true⟩

def words02 : List Nat := [360584002029463304, 360584005656179028, 360584007994327631, 360584010332272488, 360584010332458271, 360584010214631756, 360584006834761498, 360584001204949644, 360583995575741911, 360583991602681582]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360419975060393930, 360419976804034904⟩, ⟨2859942687014460699, 2859963271691728615⟩, true⟩

def words03 : List Nat := [360583992947745827, 360583995259543014, 360583995366812501, 360583995367033886, 360583994088592058, 360583990633411438, 360583987178565982, 360583982681160443, 360583974927075288, 360583965523741999]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360649871377114962, 360649873122844876⟩, ⟨(-1150611254278483168), (-1150590633160159896)⟩, true⟩

def words04 : List Nat := [360583956121437291, 360583948993304603, 360583944370744706, 360583943023265108, 360583941675918854, 360583937533638221, 360583934842098307, 360583934369497966, 360583936696646616, 360583940475251033]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360614812926778379, 360614814674620650⟩, ⟨(-538671511502808289), (-538650853513536049)⟩, true⟩

def words05 : List Nat := [360583941723751001, 360583942972126925, 360583946066003695, 360583950788184578, 360583954658187555, 360583958527783191, 360583959664404702, 360583962342808686, 360583964110018515, 360583965877099687]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360596044030858043, 360596045780783878⟩, ⟨(-211116009510872141), (-211095315131940515)⟩, true⟩

def words06 : List Nat := [360583969010922320, 360583969011143802, 360583968894961647, 360583967134626685, 360583965374460309, 360583961354256673, 360583961105974889, 360583962614602096, 360583962614801424, 360583963168733513]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360639503243191656, 360639504995212762⟩, ⟨(-970389697624847047), (-970368966631073403)⟩, true⟩

def words07 : List Nat := [360583967124748095, 360583971080379584, 360583977241466931, 360583980156022500, 360583980244752523, 360583980333490177, 360583983684233624, 360583988720033235, 360583991896205153, 360583995072060135]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360653292073218238, 360653293827349194⟩, ⟨(-1212086386115918803), (-1212065618231475909)⟩, true⟩

def words08 : List Nat := [360583996606841145, 360583996607062854, 360583996449171027, 360583998000406278, 360583998000592809, 360583997670639365, 360583997454808414, 360583994994913867, 360583993334343135, 360583997296663043]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593017622227343, 360593019378449528⟩, ⟨(-157439643058323848), (-157418838587755550)⟩, true⟩

def words09 : List Nat := [360584004516722384, 360584011735998575, 360584016030621436, 360584017085900357, 360584017291685975, 360584017497508871, 360584020959336543, 360584023501762676, 360584024016010801, 360584024530235840]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk174
