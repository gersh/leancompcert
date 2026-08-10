import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk180A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk180B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk180A

def state06 : KState := ⟨⟨360595244666340454, 360595246542142406⟩, ⟨(-201552767087563874), (-201529836302726022)⟩, true⟩

def words05 : List Nat := [360584075581982991, 360584077611197174, 360584079533636853, 360584083811034064, 360584086331700099, 360584088852124235, 360584089457465888, 360584089457695415, 360584087636212103, 360584088254323198]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603307149755809, 360603309027717923⟩, ⟨(-347076359486894563), (-347053389678421153)⟩, true⟩

def words06 : List Nat := [360584091929174953, 360584095222903939, 360584096797522929, 360584098371990658, 360584099158907576, 360584101479283870, 360584102599040746, 360584103718714196, 360584103718919168, 360584104036866370]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360692546155450206, 360692548035579427⟩, ⟨(-1960394259929896341), (-1960371250950974625)⟩, true⟩

def words07 : List Nat := [360584106094223460, 360584108151421541, 360584109493497627, 360584110948015948, 360584110948227878, 360584109779167285, 360584110493196843, 360584114424283879, 360584120421904121, 360584126418912707]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608245648150958, 360608247530473811⟩, ⟨(-436510155841501358), (-436487107191267414)⟩, true⟩

def words08 : List Nat := [360584129779096684, 360584130102392607, 360584131018376033, 360584131934325845, 360584132066836213, 360584132067066088, 360584129163704865, 360584124722813697, 360584120282364763, 360584120223680861]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360490653057156911, 360490654941643787⟩, ⟨1691529884954917746, 1691552972763200932⟩, true⟩

def words09 : List Nat := [360584123608587320, 360584126993163467, 360584128277232932, 360584128277462948, 360584127507871029, 360584123883576561, 360584120259614376, 360584119680891332, 360584116070349823, 360584110906989821]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk180B
