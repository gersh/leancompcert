import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk191A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk191B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk191A

def state06 : KState := ⟨⟨360512417491366285, 360512419614017245⟩, ⟨1378942820646174621, 1378970346728843855⟩, true⟩

def words05 : List Nat := [360584428316034734, 360584423936666601, 360584419557677060, 360584417162866919, 360584413139280828, 360584406767954086, 360584400397245883, 360584396734739347, 360584394682751381, 360584390926476997]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608098067833295, 360608100192816428⟩, ⟨(-455011774634403646), (-454984203855926590)⟩, true⟩

def words06 : List Nat := [360584387170561513, 360584382030897314, 360584378062385924, 360584376800414258, 360584375538509883, 360584373590981263, 360584372350328998, 360584369756783477, 360584367163462048, 360584367252236598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360478110485120826, 360478112612414219⟩, ⟨2037557520430546529, 2037585135508251121⟩, true⟩

def words07 : List Nat := [360584369635836530, 360584372019234139, 360584372019457487, 360584371924759530, 360584369121663156, 360584364512362628, 360584359903470778, 360584357197604168, 360584353038430407, 360584347499562721]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596097819800737, 360596099949406799⟩, ⟨(-225849829606450068), (-225822170160301262)⟩, true⟩

def words08 : List Nat := [360584341961213172, 360584339123334724, 360584339634326328, 360584341239630512, 360584341239856374, 360584340506508884, 360584338093713377, 360584335617778854, 360584333142027412, 360584332862222166]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574793570112034, 360574795702051713⟩, ⟨183043721785884235, 183071426025961653⟩, true⟩

def words09 : List Nat := [360584332862440588, 360584332126903715, 360584331565750931, 360584333819574308, 360584334217283675, 360584334614990244, 360584334615210964, 360584333533023645, 360584331168516555, 360584330672157232]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk191B
