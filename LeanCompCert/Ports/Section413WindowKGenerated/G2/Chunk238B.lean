import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk238A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk238B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk238A

def state06 : KState := ⟨⟨360564829759460597, 360564833115968021⟩, ⟨412455773166123320, 412509954318463944⟩, true⟩

def words05 : List Nat := [360582112869497425, 360582116489551542, 360582119227981666, 360582120222277047, 360582120225136851, 360582120228082908, 360582121984897307, 360582122605885863, 360582122606166910, 360582121881865694]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360642151900238582, 360642155259683619⟩, ⟨(-1432992945855529680), (-1432938694598197100)⟩, true⟩

def words06 : List Nat := [360582121673462865, 360582123433186225, 360582125118107154, 360582126802942369, 360582126805928674, 360582126806239278, 360582125066785840, 360582124231539063, 360582124312785539, 360582126827921306]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360643349529140413, 360643352891539126⟩, ⟨(-1461543614287771950), (-1461489292511277922)⟩, true⟩

def words07 : List Nat := [360582128391657172, 360582129955295851, 360582133270386407, 360582137725187810, 360582141646603472, 360582145567741047, 360582148121345373, 360582148933795090, 360582151497026383, 360582154060145497]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588216200969341, 360588219566294959⟩, ⟨(-144996057062790393), (-144941665376718817)⟩, true⟩

def words08 : List Nat := [360582155980372759, 360582156159817881, 360582156160095491, 360582155245530658, 360582154330987265, 360582152392537555, 360582152021696835, 360582152711561565, 360582152711838692, 360582152776902439]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360672713320061305, 360672716688326941⟩, ⟨(-2164292823160471015), (-2164238361223078785)⟩, true⟩

def words09 : List Nat := [360582152970844033, 360582153164858058, 360582155108019077, 360582156568275914, 360582156568565586, 360582156430223917, 360582156951241034, 360582158992400797, 360582162781677452, 360582166570707466]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk238B
