import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk687

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576529211944494, 360576559585555999⟩, ⟨428161117517720282, 429570611880311968⟩, true⟩

def state01 : KState := ⟨⟨360558718087200809, 360558748469959097⟩, ⟨1651798270590846783, 1653208393383107007⟩, true⟩

def words00 : List Nat := [360582812342662491, 360582812243664038, 360582811932976725, 360582811516564013, 360582811100021137, 360582810502644125, 360582810071794487, 360582809805528243, 360582809539164247, 360582809136432436]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588138233225149, 360588168625169028⟩, ⟨(-369749868784421199), (-368339114805329849)⟩, true⟩

def words01 : List Nat := [360582808787046173, 360582808649369631, 360582808584025696, 360582808680478737, 360582808681384163, 360582808598126008, 360582808514689181, 360582808546604574, 360582808625402825, 360582808704405283]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588651129250705, 360588681530446040⟩, ⟨(-405165335649697865), (-403753945865130313)⟩, true⟩

def words02 : List Nat := [360582808705271149, 360582808678457387, 360582808439975583, 360582808294976044, 360582808149712718, 360582807950771775, 360582807758406616, 360582807447467541, 360582807136344769, 360582807122306116]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360542301073541223, 360542331483900277⟩, ⟨2780715548230176915, 2782127567883981967⟩, true⟩

def words03 : List Nat := [360582807166097384, 360582807210067623, 360582807210956929, 360582807092732939, 360582806762949302, 360582806336754993, 360582805910288001, 360582805695267501, 360582805268760574, 360582804680989076]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574062978564124, 360574093398102030⟩, ⟨597256738406636130, 598669389058282664⟩, true⟩

def words04 : List Nat := [360582804092997168, 360582803651787820, 360582803353068833, 360582803265764712, 360582803178383003, 360582802910701304, 360582802524344524, 360582802051431753, 360582801578244742, 360582801316488333]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360574204511441982, 360574234940239070⟩, ⟨587547567541582412, 588960854807967690⟩, true⟩

def words05 : List Nat := [360582801190703857, 360582800958825573, 360582800726767954, 360582800770455098, 360582800819822962, 360582800869347900, 360582800870219048, 360582800759324792, 360582800521149817, 360582800397697011]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559011190279531, 360559041628248131⟩, ⟨1632150050136115806, 1633563968081649010⟩, true⟩

def words06 : List Nat := [360582800273935860, 360582799987179570, 360582799489084116, 360582798885440420, 360582798281658040, 360582797551259053, 360582796943556754, 360582796547133810, 360582796150608442, 360582795648432538]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592879510982514, 360592909958125688⟩, ⟨(-697173908202014667), (-695759359275597829)⟩, true⟩

def words07 : List Nat := [360582795303811448, 360582795170532965, 360582795056401911, 360582795057374597, 360582794920576676, 360582794580587753, 360582794240422547, 360582794111565870, 360582794235114979, 360582794383195467]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569260493598830, 360569290950014789⟩, ⟨927404168896544801, 928819355650994907⟩, true⟩

def words08 : List Nat := [360582794400124403, 360582794503516806, 360582794504312864, 360582794498031723, 360582794491493248, 360582794432024010, 360582794215061659, 360582793892163017, 360582793569101080, 360582793193882372]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565027487324011, 360565057952909250⟩, ⟨1218705397845494491, 1220121215398078613⟩, true⟩

def words09 : List Nat := [360582793013038438, 360582793028659527, 360582793029527570, 360582792909061005, 360582792835701395, 360582792709580370, 360582792616107781, 360582792617081155, 360582792529661735, 360582792272900502]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk687
