import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk542A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk542B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk542A

def state06 : KState := ⟨⟨362478199861715199, 362478242684317557⟩, ⟨362383795758702464, 363953468398196840⟩, true⟩

def words05 : List Nat := [371284951679759757, 371284951611274692, 371284951763748214, 371284951765570289, 371284951536465752, 371284951253185800, 371284950969175726, 371284950764529698, 371284950389183009, 371284950267590654]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468489445460454, 362468532284523842⟩, ⟨889252429976916005, 890822995872929181⟩, true⟩

def words06 : List Nat := [371284950145349073, 371284950022624480, 371284949574139561, 371284949299677938, 371284949024261815, 371284948853281577, 371284948287889008, 371284947723599967, 371284947158607758, 371284946933425131]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362462501379648666, 362462544235156592⟩, ⟨1214285011468519470, 1215856469893340596⟩, true⟩

def words07 : List Nat := [371284946632226495, 371284946473236150, 371284946313610815, 371284946139224825, 371284945660892239, 371284945237213872, 371284944812627517, 371284944727518205, 371284944359655905, 371284943949045563]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471392699526037, 362471435571357378⟩, ⟨731623812439832954, 733196156979253242⟩, true⟩

def words08 : List Nat := [371284943537624908, 371284943279923589, 371284942876406944, 371284942726509632, 371284942576101580, 371284942305300526, 371284941582033440, 371284941198524321, 371284940814028162, 371284940750156039]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475031312496469, 362475074200929778⟩, ⟨534117916852242956, 535691162797877880⟩, true⟩

def words09 : List Nat := [371284940502764319, 371284940256507218, 371284940099916469, 371284940101925674, 371284940048442815, 371284940074992328, 371284940099195664, 371284940101024244, 371284939779322814, 371284939599876332]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk542B
