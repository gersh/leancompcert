import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk852

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474634849431966, 362474744228706400⟩, ⟨892636745691336120, 898929154175848880⟩, true⟩

def state01 : KState := ⟨⟨362480886805055366, 362480996210687345⟩, ⟨359978687002228061, 366273341288034933⟩, true⟩

def words00 : List Nat := [371285294932361942, 371285294935339309, 371285294854032949, 371285294774058762, 371285294692914503, 371285294655215951, 371285294605646850, 371285294646375980, 371285294685984943, 371285294689050073]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488825016354800, 362488934448765759⟩, ⟨(-316494465769113798), (-310197529511270490)⟩, true⟩

def words01 : List Nat := [371285294640650223, 371285294622689584, 371285294719281493, 371285294722242464, 371285294670255809, 371285294601716105, 371285294531944951, 371285294512419402, 371285294483843668, 371285294529854795]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478858293725569, 362478967752855466⟩, ⟨532868245335388563, 539167458716689141⟩, true⟩

def words02 : List Nat := [371285294554022111, 371285294556983450, 371285294397419730, 371285294376994348, 371285294355115453, 371285294341146816, 371285294166512869, 371285293992809019, 371285293817893362, 371285293781938145]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476802995036670, 362476912480889904⟩, ⟨708096354855796231, 714397846003640081⟩, true⟩

def words03 : List Nat := [371285293739280481, 371285293772143832, 371285293803831213, 371285293806799271, 371285293695840401, 371285293628534255, 371285293626435905, 371285293629410328, 371285293592353323, 371285293497384551]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362495834689388442, 362495944201763332⟩, ⟨(-914267979860066132), (-907964227875938110)⟩, true⟩

def words04 : List Nat := [371285293401081744, 371285293380938144, 371285293336329939, 371285293384965485, 371285293410377895, 371285293413391694, 371285293370760989, 371285293420819466, 371285293591891093, 371285293719917067]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492399953751535, 362492509493097033⟩, ⟨(-621447773501121462), (-615141722136316972)⟩, true⟩

def words05 : List Nat := [371285293843307364, 371285293967668624, 371285294127499726, 371285294236756972, 371285294344069499, 371285294452534990, 371285294560293496, 371285294563256982, 371285294597038088, 371285294685363881]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473592471896686, 362473702037604308⟩, ⟨982177242586166669, 988485541725092733⟩, true⟩

def words06 : List Nat := [371285294811039823, 371285294814002725, 371285294772870789, 371285294723190629, 371285294672337119, 371285294664872160, 371285294588394264, 371285294545413930, 371285294501461555, 371285294456294646]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498013586444045, 362498123178981451⟩, ⟨(-1100328444307633523), (-1094017857266796229)⟩, true⟩

def words07 : List Nat := [371285294322356265, 371285294310234054, 371285294407533746, 371285294410548441, 371285294409801401, 371285294386153547, 371285294453313454, 371285294483549452, 371285294635989332, 371285294789806057]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474785217705365, 362474894836995272⟩, ⟨880671545996495823, 886984414627563253⟩, true⟩

def words08 : List Nat := [371285294922700643, 371285294925664003, 371285294893301776, 371285294915078127, 371285294960277594, 371285294963241053, 371285294825344544, 371285294688430154, 371285294550237050, 371285294466666131]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468247949764812, 362468357595691796⟩, ⟨1438307880870489837, 1444623021517135741⟩, true⟩

def words09 : List Nat := [371285294346749556, 371285294314726833, 371285294281764594, 371285294248355221, 371285294090718967, 371285293941675516, 371285293791058231, 371285293778748097, 371285293582509054, 371285293387268785]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk852
