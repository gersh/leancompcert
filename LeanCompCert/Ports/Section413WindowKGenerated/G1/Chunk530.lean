import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk530

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494034838974989, 362494075618736224⟩, ⟨(-481874010117589737), (-480413900591058163)⟩, true⟩

def state01 : KState := ⟨⟨362477159840272093, 362477200636084498⟩, ⟨412552835543882503, 414013795864041273⟩, true⟩

def words00 : List Nat := [371285011537446645, 371285011539223574, 371285011266808940, 371285011309899340, 371285011461273493, 371285011463055437, 371285011251536959, 371285011040726323, 371285010829187071, 371285010743533358]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469913973516650, 362469954785328281⟩, ⟨796714052166703240, 798175860688311208⟩, true⟩

def words01 : List Nat := [371285010597633561, 371285010599750356, 371285010601080028, 371285010570150822, 371285010198306314, 371285009871474265, 371285009570117385, 371285009571926197, 371285009308330214, 371285009026382380]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470710926841729, 362470751754551434⟩, ⟨754512096984604449, 755974748504595081⟩, true⟩

def words02 : List Nat := [371285008743659500, 371285008733708360, 371285008579313816, 371285008615215224, 371285008616616881, 371285008549756915, 371285008008642186, 371285007704753086, 371285007399955686, 371285007359840980]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468311365939502, 362468352209886514⟩, ⟨881814639185096584, 883278151848847698⟩, true⟩

def words03 : List Nat := [371285007092362997, 371285006759160243, 371285006425198510, 371285006427011798, 371285006250550443, 371285006183754873, 371285006116391351, 371285006039073550, 371285005578782984, 371285005267048069]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465464277964890, 362465505137743873⟩, ⟨1032851921175392807, 1034316273649646143⟩, true⟩

def words04 : List Nat := [371285004954291238, 371285004813507244, 371285004354124047, 371285003895423997, 371285003436077238, 371285003067029539, 371285002570102203, 371285002428849610, 371285002286983107, 371285002145729729]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477458084748738, 362477498960603439⟩, ⟨396514192540521245, 397979397914071655⟩, true⟩

def words05 : List Nat := [371285001779422101, 371285001768892983, 371285001757498659, 371285001744225848, 371285001319640696, 371285000833591159, 371285000346815365, 371285000084256854, 371284999654001337, 371284999514653837]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470423913443254, 362470464805341998⟩, ⟨769708546182736002, 771174602932969810⟩, true⟩

def words06 : List Nat := [371284999374628760, 371284999207636696, 371284998627672329, 371284998351808468, 371284998075026213, 371284997907771877, 371284997414824688, 371284996850960147, 371284996286410222, 371284996077302296]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469718964469220, 362469759872396850⟩, ⟨807217477466416343, 808684384953080921⟩, true⟩

def words07 : List Nat := [371284995847928229, 371284995893108209, 371284995938071904, 371284995939887076, 371284995759647217, 371284995600372539, 371284995633318319, 371284995635097822, 371284995356826155, 371284995071811942]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495938828239327, 362495979752125428⟩, ⟨(-584667114650130360), (-583199360007701182)⟩, true⟩

def words08 : List Nat := [371284994786022647, 371284994648502102, 371284994349010044, 371284994363820777, 371284994365198370, 371284994321957668, 371284994126909455, 371284994208148085, 371284994642729768, 371284994851482990]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487022685174517, 362487063625258707⟩, ⟨(-111228804352968064), (-109760189672131628)⟩, true⟩

def words09 : List Nat := [371284995005621059, 371284995160330308, 371284995668615683, 371284996000465199, 371284996275238034, 371284996550674116, 371284996759694902, 371284996761475233, 371284996576164843, 371284996617298930]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk530
