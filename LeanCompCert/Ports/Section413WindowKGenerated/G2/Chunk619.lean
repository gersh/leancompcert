import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk619

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

def state06 : KState := ⟨⟨360556642967405697, 360556667470944728⟩, ⟨1607034632651570506, 1608060268756471258⟩, true⟩

def words05 : List Nat := [360582621274262524, 360582621622388585, 360582621828058011, 360582621828927057, 360582621775028705, 360582621654857971, 360582621534439839, 360582621349989898, 360582621088869719, 360582620670892380]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578586862534662, 360578611374272019⟩, ⟨247295737985337058, 248321882099174054⟩, true⟩

def words06 : List Nat := [360582620252731583, 360582620104587279, 360582620105295025, 360582620070472203, 360582620035578033, 360582619749849004, 360582619204535623, 360582618919786312, 360582618634791832, 360582618504852932]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590436666278572, 360590461186307455⟩, ⟨(-487187072963015125), (-486160414983103411)⟩, true⟩

def words07 : List Nat := [360582618440983090, 360582618155693917, 360582617870248064, 360582617777729504, 360582617778458404, 360582617686649958, 360582617594749430, 360582617364406223, 360582617358033285, 360582617485576859]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594293879915771, 360594318408126506⟩, ⟨(-726278343960180540), (-725251178827602576)⟩, true⟩

def words08 : List Nat := [360582617873003427, 360582618174115587, 360582618301466191, 360582618428904507, 360582618429651084, 360582618294805665, 360582618542604711, 360582618797081019, 360582618920553975, 360582619110182811]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594583905229038, 360594608441663272⟩, ⟨(-744175369211099132), (-743147694263999018)⟩, true⟩

def words09 : List Nat := [360582619559710643, 360582620009506027, 360582620636254593, 360582621073098804, 360582621290031731, 360582621507031414, 360582621685605500, 360582621993580870, 360582622187627984, 360582622381853528]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk619
