import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk464

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499882970063655, 362499913890935417⟩, ⟨(-672523932858989399), (-671554584994993829)⟩, true⟩

def state01 : KState := ⟨⟨362466242817360949, 362466273752139624⟩, ⟨888476479042039461, 889446472257493671⟩, true⟩

def words00 : List Nat := [371285441357446073, 371285441358985836, 371285441054275776, 371285440936614379, 371285440840484152, 371285440842023967, 371285440247215169, 371285439660508882, 371285439073196169, 371285438726762712]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362447899537496179, 362447930486116933⟩, ⟨1740018041481241913, 1740988677179757647⟩, true⟩

def words01 : List Nat := [371285438365142099, 371285438417072044, 371285438472807488, 371285438474350242, 371285438031718599, 371285437731729751, 371285437430957057, 371285437241661257, 371285436434047875, 371285435627805425]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362456390413556684, 362456421375954639⟩, ⟨1345900673993852543, 1346871949301172941⟩, true⟩

def words02 : List Nat := [371285434820916612, 371285434408483057, 371285433765004907, 371285433428497464, 371285433091484394, 371285432682326903, 371285431710807737, 371285431036040558, 371285430360522398, 371285430033057831]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362464975035856488, 362465006012350067⟩, ⟨947223950763368217, 948195880597436037⟩, true⟩

def words03 : List Nat := [371285429409480163, 371285428597912098, 371285427785731871, 371285427350652773, 371285426714976716, 371285426155604348, 371285425595740221, 371285425005933866, 371285424104694715, 371285423666971029]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362464660171953821, 362464691162168785⟩, ⟨961912751715228103, 962885318843377179⟩, true⟩

def words04 : List Nat := [371285423251302485, 371285423252854509, 371285422860917869, 371285422468107942, 371285422074753813, 371285421703118725, 371285421098779566, 371285420957625180, 371285420815953542, 371285420663112669]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482397061204226, 362482428065351991⟩, ⟨137958922277443920, 138932136654823546⟩, true⟩

def words05 : List Nat := [371285420234099232, 371285420252164275, 371285420385204661, 371285420386746664, 371285419902912611, 371285419362957585, 371285418822386085, 371285418744853511, 371285418488235709, 371285418425589934]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478375794091479, 362478406812156415⟩, ⟨324742516596193974, 325716377635884494⟩, true⟩

def words06 : List Nat := [371285418362383563, 371285418237962842, 371285417670868462, 371285417493657341, 371285417315657663, 371285417279702407, 371285416858883387, 371285416439613415, 371285416019749832, 371285415987487508]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472474599837452, 362472505631831731⟩, ⟨599077714639827629, 600052223046582981⟩, true⟩

def words07 : List Nat := [371285416148927039, 371285416461823141, 371285416679831029, 371285416681377084, 371285416419758569, 371285416155060087, 371285416085024296, 371285416086571309, 371285415809334446, 371285415533360272]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480747699741717, 362480778745532005⟩, ⟨214561324677668973, 215536474394209621⟩, true⟩

def words08 : List Nat := [371285415371633677, 371285415373333930, 371285415419994492, 371285415555593802, 371285415619203231, 371285415620756760, 371285415269165304, 371285415004393268, 371285414933962467, 371285414935559844]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482219227128207, 362482250286965495⟩, ⟨146166235263926071, 147142038094371475⟩, true⟩

def words09 : List Nat := [371285414836991700, 371285414739646962, 371285414885342893, 371285414972377319, 371285415088382866, 371285415204992018, 371285415225117014, 371285415226660794, 371285414698025623, 371285414631870751]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk464
