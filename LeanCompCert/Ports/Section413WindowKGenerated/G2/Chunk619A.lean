import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk619A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565938362817828, 360565962817027413⟩, ⟨1029900063526696560, 1030922644663214164⟩, true⟩

def state01 : KState := ⟨⟨360598143701974252, 360598168164393311⟩, ⟨(-963860119075938744), (-962837029734020674)⟩, true⟩

def words00 : List Nat := [360582617195614079, 360582616843350954, 360582616647314585, 360582616646720053, 360582616646057505, 360582616424775097, 360582616126846043, 360582615984122972, 360582615958200359, 360582616210302213]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574240212542016, 360574264683235034⟩, ⟨516199566487581050, 517223168110903676⟩, true⟩

def words01 : List Nat := [360582616329999126, 360582616449779353, 360582616761027444, 360582617258452192, 360582617533417421, 360582617808503358, 360582617952328666, 360582617953197319, 360582617904478753, 360582617770575327]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591921481576430, 360591945960454844⟩, ⟨(-578744763074761269), (-577720654569472929)⟩, true⟩

def words02 : List Nat := [360582617636379946, 360582617615484800, 360582617601246142, 360582617455998726, 360582617310615048, 360582617099890188, 360582617196978919, 360582617376334769, 360582617377129286, 360582617503711542]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360619000519875485, 360619025006951165⟩, ⟨(-2255932850844711503), (-2254908234643599829)⟩, true⟩

def words03 : List Nat := [360582617743314188, 360582617983166559, 360582618483298591, 360582618783498536, 360582618863213263, 360582618943008745, 360582619232230989, 360582619699567587, 360582620288022099, 360582620876655504]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594591854842421, 360594616350203232⟩, ⟨(-744153635817523328), (-743128506395544310)⟩, true⟩

def words04 : List Nat := [360582621268309476, 360582621400426116, 360582621525642151, 360582621651097669, 360582621651828264, 360582621633892866, 360582621440978884, 360582621118069799, 360582620795002339, 360582620926297314]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk619A
