import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk778

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585670450542119, 360585709789365213⟩, ⟨(-274854632739540270), (-272787528681905372)⟩, true⟩

def state01 : KState := ⟨⟨360594244652700234, 360594284002005646⟩, ⟨(-941921548759059313), (-939853629127115783)⟩, true⟩

def words00 : List Nat := [360582203778969634, 360582204072856850, 360582204387093978, 360582204701529823, 360582204877540928, 360582204888821647, 360582204989012014, 360582205089524968, 360582205172566468, 360582205328950074]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598858631883178, 360598897991781388⟩, ⟨(-1300947577086384097), (-1298878833177670743)⟩, true⟩

def words01 : List Nat := [360582205378502116, 360582205428193004, 360582205642615343, 360582205985681841, 360582206266419886, 360582206547331839, 360582206745543274, 360582206965130945, 360582207180527304, 360582207396271466]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603502465654978, 360603541836011382⟩, ⟨(-1662396122075406021), (-1660326564257912561)⟩, true⟩

def words02 : List Nat := [360582207723709167, 360582207924432035, 360582208041589912, 360582208158858856, 360582208170288468, 360582208327398264, 360582208613163082, 360582208899133289, 360582209102440674, 360582209377681695]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360613349852366290, 360613389233224900⟩, ⟨(-2428958674815351861), (-2426888299559081835)⟩, true⟩

def words03 : List Nat := [360582209701920653, 360582210026486718, 360582210346782311, 360582210502591984, 360582210517403746, 360582210532310046, 360582210686433436, 360582210923372658, 360582211324814608, 360582211726518164]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587378016506814, 360587417407958453⟩, ⟨(-407321396006294732), (-405250196137557110)⟩, true⟩

def words04 : List Nat := [360582212036982151, 360582212182905080, 360582212306481072, 360582212430381441, 360582212512654075, 360582212513765333, 360582212431485445, 360582212193399568, 360582211955106468, 360582211948861749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360577916172034427, 360577955573950307⟩, ⟨329398933254280799, 331470947817185951⟩, true⟩

def words05 : List Nat := [360582212146135981, 360582212343617907, 360582212458507920, 360582212618744819, 360582212693257086, 360582212768060639, 360582212843867222, 360582212895263328, 360582212896263535, 360582212842738096]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595319223572608, 360595358635998321⟩, ⟨(-1025704451513057168), (-1023631618603661036)⟩, true⟩

def words06 : List Nat := [360582212788974977, 360582212746146728, 360582212939200364, 360582213132461888, 360582213182283304, 360582213183394963, 360582213117480459, 360582213167695274, 360582213243566793, 360582213413532915]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586763855965862, 360586803278971701⟩, ⟨(-359463257849702911), (-357389601014123247)⟩, true⟩

def words07 : List Nat := [360582213485291336, 360582213557169833, 360582213734727758, 360582213995046747, 360582214132512789, 360582214270139088, 360582214293302876, 360582214294416274, 360582214299766866, 360582214359966885]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587474911629461, 360587514345113418⟩, ⟨(-414839044902898404), (-412764571977144218)⟩, true⟩

def words08 : List Nat := [360582214492992233, 360582214630526281, 360582214662346177, 360582214694281663, 360582214695212866, 360582214680843504, 360582214835159204, 360582214989683738, 360582215017065661, 360582215086251969]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617236905262080, 360617276349245460⟩, ⟨(-2733219453406565658), (-2731144162629867640)⟩, true⟩

def words09 : List Nat := [360582215129065825, 360582215172198693, 360582215379618230, 360582215611950605, 360582215700636716, 360582215789421052, 360582215993437890, 360582216280147058, 360582216731111328, 360582217182320391]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk778
