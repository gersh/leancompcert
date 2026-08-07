import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk989

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604831684973075, 360604896450708177⟩, ⟨(-2226542632460111576), (-2222217571851082232)⟩, true⟩

def state01 : KState := ⟨⟨360591498281564026, 360591563061021314⟩, ⟨(-907948942152575533), (-903622524356401031)⟩, true⟩

def words00 : List Nat := [360582427480051840, 360582427518864448, 360582427537219917, 360582427555984364, 360582427557187174, 360582427535250160, 360582427478078410, 360582427369841753, 360582427261331520, 360582427347861439]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568725787420408, 360568790580402324⟩, ⟨1344682096342442938, 1349009851929336066⟩, true⟩

def words01 : List Nat := [360582427543534973, 360582427739489989, 360582427884060295, 360582427995387913, 360582428067303724, 360582428139599250, 360582428169481537, 360582428170919083, 360582428099025802, 360582427962649892]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581379841203756, 360581444647755006⟩, ⟨92828055681361791, 97157153614996443⟩, true⟩

def words02 : List Nat := [360582427825951371, 360582427751376296, 360582427727335918, 360582427646654606, 360582427565839515, 360582427398036468, 360582427128095834, 360582426960717919, 360582426792904733, 360582426727544908]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585776472928444, 360585841293185496⟩, ⟨(-342217344069511444), (-337886890155298050)⟩, true⟩

def words03 : List Nat := [360582426718921332, 360582426632454770, 360582426545717403, 360582426460568033, 360582426452835188, 360582426403916585, 360582426354853781, 360582426254818624, 360582426222911662, 360582426259072689]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584227109542225, 360584291943332498⟩, ⟨(-188941030630328247), (-184609237672459031)⟩, true⟩

def words04 : List Nat := [360582426375723734, 360582426421907870, 360582426423195526, 360582426393705740, 360582426364011291, 360582426239101361, 360582426223219485, 360582426267177551, 360582426268458481, 360582426280148979]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk989
