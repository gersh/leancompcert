import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk967A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591999052888004, 360592060861787709⟩, ⟨(-945315507766509749), (-941279638396609821)⟩, true⟩

def state01 : KState := ⟨⟨360599267550671132, 360599329372806187⟩, ⟨(-1648228366866854791), (-1644191217573120237)⟩, true⟩

def words00 : List Nat := [360582327026340071, 360582327176715865, 360582327433617395, 360582327690782617, 360582327846313339, 360582327895333324, 360582327943397356, 360582327991866686, 360582328117937272, 360582328295187580]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580383005089123, 360580444840611666⟩, ⟨178223752565852210, 182262196627982450⟩, true⟩

def words01 : List Nat := [360582328418473416, 360582328541944176, 360582328701353855, 360582328913868835, 360582329053006538, 360582329192367602, 360582329271366640, 360582329288643861, 360582329289798642, 360582329271925024]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586332569256254, 360586394417989917⟩, ⟨(-397283850199025489), (-393244128292613015)⟩, true⟩

def words02 : List Nat := [360582329331726402, 360582329333129923, 360582329330441349, 360582329245670115, 360582329160673494, 360582329026931872, 360582329017674784, 360582329059653373, 360582329060906404, 360582329080835411]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609451490866094, 360609513352863800⟩, ⟨(-2633744546916630124), (-2629703541912054352)⟩, true⟩

def words03 : List Nat := [360582329230877147, 360582329381342567, 360582329488077438, 360582329578638669, 360582329579933183, 360582329580081366, 360582329685577610, 360582329861255365, 360582330143385335, 360582330425853411]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604084279420094, 360604146154798635⟩, ⟨(-2114597513478464958), (-2110555213949488234)⟩, true⟩

def words04 : List Nat := [360582330654295776, 360582330776369512, 360582330979957439, 360582331183954822, 360582331319175994, 360582331442554608, 360582331469092155, 360582331495760353, 360582331629004288, 360582331856094235]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk967A
