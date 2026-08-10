import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk989A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk989B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk989A

def state06 : KState := ⟨⟨360588743114590613, 360588807961977732⟩, ⟨(-635797958805353879), (-631464820373662835)⟩, true⟩

def words05 : List Nat := [360582426370952131, 360582426462207974, 360582426655075574, 360582426746397709, 360582426750637991, 360582426754993188, 360582426793890139, 360582426884109439, 360582426949773725, 360582427015742613]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580899675952620, 360580964537026822⟩, ⟨140373960775272410, 144708453751074740⟩, true⟩

def words06 : List Nat := [360582427030348622, 360582427031786783, 360582426958044632, 360582426973216747, 360582426974420199, 360582426963597177, 360582426954720131, 360582426868906010, 360582426782825021, 360582426681653993]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573103066599352, 360573167941235635⟩, ⟨912058371399370279, 916394206681113427⟩, true⟩

def words07 : List Nat := [360582426698088699, 360582426729569619, 360582426730885490, 360582426683616940, 360582426650605749, 360582426566185589, 360582426481345662, 360582426451905403, 360582426410776294, 360582426318753125]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584060708002108, 360584125596210254⟩, ⟨(-172535648429955842), (-168198469740018516)⟩, true⟩

def words08 : List Nat := [360582426234852832, 360582426313036965, 360582426437247676, 360582426561730726, 360582426599468707, 360582426600907734, 360582426573878646, 360582426527567974, 360582426480843362, 360582426467302172]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584416843223692, 360584481745146357⟩, ⟨(-207792645760546084), (-203454109403300192)⟩, true⟩

def words09 : List Nat := [360582426468599169, 360582426416478133, 360582426412508253, 360582426541618711, 360582426614457518, 360582426687523950, 360582426709322298, 360582426710760968, 360582426651462289, 360582426673890478]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk989B
