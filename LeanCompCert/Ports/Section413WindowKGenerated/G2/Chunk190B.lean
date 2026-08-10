import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk190A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk190B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk190A

def state06 : KState := ⟨⟨360459077293178666, 360459079392736898⟩, ⟨2397260328536602938, 2397287413317521214⟩, true⟩

def words05 : List Nat := [360584884941574656, 360584884312707544, 360584883683880400, 360584881303173775, 360584879040316041, 360584875291224782, 360584871542457066, 360584867053325709, 360584861826679768, 360584855227643379]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360482170620888117, 360482172722746722⟩, ⟨1956800608618427328, 1956827737256020008⟩, true⟩

def words06 : List Nat := [360584848629247968, 360584841869944439, 360584836556897883, 360584831660028306, 360584826763653563, 360584819436824709, 360584809370183203, 360584800537657373, 360584791705982496, 360584785608811537]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360483551183269386, 360483553287449161⟩, ⟨1930477016480180575, 1930504189393742305⟩, true⟩

def words07 : List Nat := [360584780228459656, 360584772999127166, 360584765770506276, 360584761275381437, 360584759249298686, 360584755318570609, 360584751388227511, 360584746090055287, 360584738055207033, 360584732752302083]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561178044829878, 360561180151307397⟩, ⟨449079969211848332, 449107185977798240⟩, true⟩

def words08 : List Nat := [360584727449870250, 360584724878778805, 360584723442831426, 360584720640086271, 360584717837595382, 360584713147981194, 360584709855421655, 360584709292561914, 360584708729740351, 360584705933705396]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588036772501706, 360588038881281500⟩, ⟨(-63939424534138624), (-63912163806532158)⟩, true⟩

def words09 : List Nat := [360584704701606198, 360584704381894873, 360584705554889289, 360584705555133183, 360584704314272239, 360584700730240994, 360584697146533588, 360584694143341975, 360584692694442080, 360584692869878614]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk190B
