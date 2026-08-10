import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk174A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk174A
