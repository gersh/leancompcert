import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk542

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499362475804974, 362499405199996234⟩, ⟨(-784432469903796677), (-782868134107518257)⟩, true⟩

def state01 : KState := ⟨⟨362479619332213713, 362479662072850753⟩, ⟨285669607456545449, 287234834696252005⟩, true⟩

def words00 : List Nat := [371284961581976732, 371284961583797463, 371284961431026414, 371284961498946630, 371284961632037641, 371284961633857756, 371284961313783183, 371284960986535557, 371284960658486118, 371284960630952511]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362458184938998887, 362458227695990934⟩, ⟨1447805100664588104, 1449371214594124388⟩, true⟩

def words01 : List Nat := [371284960680331103, 371284960828165275, 371284960934526167, 371284960936346713, 371284960589525837, 371284960258483757, 371284959932850953, 371284959934671585, 371284959489359713, 371284958998362645]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470886943196567, 362470929716513736⟩, ⟨759076548921987007, 760643548083006663⟩, true⟩

def words02 : List Nat := [371284958506592117, 371284958291162682, 371284957952889244, 371284957765847090, 371284957578236928, 371284957334619339, 371284956737639004, 371284956448035298, 371284956157541377, 371284955966708887]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480672411122174, 362480715201045407⟩, ⟨228387308632350846, 229955208422373996⟩, true⟩

def words03 : List Nat := [371284955709432003, 371284955453370853, 371284955256891534, 371284955258920154, 371284955209438773, 371284955238078021, 371284955244985698, 371284955246807976, 371284954864103328, 371284954788221336]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462674167045498, 362462716973212231⟩, ⟨1204686216907177123, 1206254997828876355⟩, true⟩

def words04 : List Nat := [371284954806176748, 371284954807999530, 371284954513470016, 371284954124323841, 371284953734514305, 371284953414164951, 371284952923026123, 371284952646271914, 371284952368904241, 371284952088379584]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk542
