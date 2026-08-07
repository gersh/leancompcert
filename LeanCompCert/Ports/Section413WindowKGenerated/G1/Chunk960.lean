import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk960

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494036016442270, 362494176169247155⟩, ⟨(-864863241755760969), (-855779186208849649)⟩, true⟩

def state01 : KState := ⟨⟨362487352168472141, 362487492351218291⟩, ⟨(-223148766186379586), (-214061836118254010)⟩, true⟩

def words00 : List Nat := [371285262099382238, 371285262186991620, 371285262274259760, 371285262362609998, 371285262449284610, 371285262483301881, 371285262578220351, 371285262674556544, 371285262769187648, 371285262795895274]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496748567414960, 362496888780618087⟩, ⟨(-1125307851817597658), (-1116217997424048840)⟩, true⟩

def words01 : List Nat := [371285262912350793, 371285263030625898, 371285263255715658, 371285263352166630, 371285263420828646, 371285263490591599, 371285263667560027, 371285263804493546, 371285263927903510, 371285264052720815]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495143376329192, 362495283619916924⟩, ⟨(-971216996058397240), (-962124223979298936)⟩, true⟩

def words02 : List Nat := [371285264165979431, 371285264169348175, 371285264239721266, 371285264327077129, 371285264422292563, 371285264447647672, 371285264471594630, 371285264496648929, 371285264619615594, 371285264727851036]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484356582567773, 362484496856525578⟩, ⟨64708318091400508, 73804006761202196⟩, true⟩

def words03 : List Nat := [371285264891970329, 371285265057494076, 371285265188916648, 371285265192284213, 371285265195684558, 371285265216469203, 371285265333651752, 371285265337022134, 371285265332185200, 371285265328066199]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489177481572927, 362489317785678708⟩, ⟨(-398302173734811066), (-389203589504143830)⟩, true⟩

def words04 : List Nat := [371285265369593331, 371285265373304980, 371285265470746074, 371285265576247014, 371285265666872686, 371285265670240742, 371285265616010810, 371285265608436231, 371285265688586009, 371285265734273683]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494718973295510, 362494859308022409⟩, ⟨(-930577467169491884), (-921475941620017860)⟩, true⟩

def words05 : List Nat := [371285265773990116, 371285265814840944, 371285265962860741, 371285266072823962, 371285266213916707, 371285266356327917, 371285266494751880, 371285266498120321, 371285266591606467, 371285266695603009]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483871749846329, 362484012114636473⟩, ⟨111447291568142817, 120551705144045569⟩, true⟩

def words06 : List Nat := [371285266842648145, 371285266864676944, 371285266867212823, 371285266857020180, 371285266864124425, 371285266867875831, 371285266868349530, 371285266905134906, 371285266943078829, 371285266946583429]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502504667913874, 362502645063152492⟩, ⟨(-1678715771915495550), (-1669608432998950148)⟩, true⟩

def words07 : List Nat := [371285267000553311, 371285267069358540, 371285267237810036, 371285267312451003, 371285267357041202, 371285267402575787, 371285267526610250, 371285267602723295, 371285267785871940, 371285267970563958]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486030716259376, 362486171141916627⟩, ⟨(-95818454270818647), (-86708192574640509)⟩, true⟩

def words08 : List Nat := [371285268153484429, 371285268247297728, 371285268390181790, 371285268534807483, 371285268683703713, 371285268700933239, 371285268716858454, 371285268733952489, 371285268773699389, 371285268786934635]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483764336196085, 362483904792185801⟩, ⟨122015273735125127, 131128450224249791⟩, true⟩

def words09 : List Nat := [371285268898609699, 371285269011624511, 371285269123038515, 371285269126413211, 371285269144859141, 371285269173374911, 371285269308400445, 371285269311770328, 371285269302625046, 371285269292188135]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk960
