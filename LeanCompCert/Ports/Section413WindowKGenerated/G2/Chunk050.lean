import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk050

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360798931939805656, 360798932066381238⟩, ⟨(-1145687494131680426), (-1145687064444635920)⟩, true⟩

def state01 : KState := ⟨⟨360697771745090143, 360697771872203606⟩, ⟨(-640866590155322044), (-640866157776169708)⟩, true⟩

def words00 : List Nat := [360569866367603270, 360569877231618525, 360569927593020051, 360569977934313961, 360569988606272367, 360569988606328958, 360569960060286981, 360569911712277219, 360569863383561248, 360569880002761146]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360463250079786227, 360463250207434529⟩, ⟨536350175785226474, 536350610846617422⟩, true⟩

def words01 : List Nat := [360569944905674446, 360570009782705568, 360570053492661230, 360570082722881209, 360570083802432943, 360570084881569530, 360570103982980982, 360570114246146218, 360570114246197646, 360570092958599194]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360990484639730462, 360990484767914693⟩, ⟨(-2112261329468695359), (-2112260891714252525)⟩, true⟩

def words02 : List Nat := [360570089660980292, 360570129508526957, 360570208576939209, 360570287613892194, 360570331292024555, 360570377521215079, 360570428427318146, 360570479313192271, 360570552185010150, 360570635654077633]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360889777679265752, 360889777807993478⟩, ⟨(-1606129763135813150), (-1606129322644927604)⟩, true⟩

def words03 : List Nat := [360570692508891094, 360570749341117431, 360570804384583385, 360570879555414944, 360570933046241037, 360570986515837123, 360571013844997674, 360571038112972173, 360571101355021383, 360571164571999642]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360656487446082828, 360656487575347393⟩, ⟨(-429130322127328605), (-429129878928097675)⟩, true⟩

def words04 : List Nat := [360571257245711382, 360571311339883557, 360571341139665072, 360571370927639436, 360571390131502954, 360571433276588370, 360571471061976509, 360571508832407183, 360571511361639253, 360571528185339851]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361186049418513337, 361186049548316835⟩, ⟨(-3106212272860155446), (-3106211826936607276)⟩, true⟩

def words05 : List Nat := [360571583803706129, 360571639400074830, 360571714015625383, 360571801002768644, 360571853887134619, 360571906750589820, 360571969648325510, 360572052349765284, 360572173693131515, 360572294988558565]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361006205424896242, 361006205555245084⟩, ⟨(-2197240845390540079), (-2197240396704808973)⟩, true⟩

def words06 : List Nat := [360572385577505281, 360572437860880859, 360572511810278069, 360572585730491564, 360572649154502750, 360572703967577199, 360572738290027148, 360572772598941706, 360572824806322809, 360572910268969240]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573002602468413, 360573002733357087⟩, ⟨1615975896177435, 1616427321596933⟩, true⟩

def words07 : List Nat := [360573000502966617, 360573090701400304, 360573156018500395, 360573206091290295, 360573225141146354, 360573244183512694, 360573301598967031, 360573320990250237, 360573320990301424, 360573320927711733]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360744739939702667, 360744740071134508⟩, ⟨(-870942124879413663), (-870941670692010559)⟩, true⟩

def words08 : List Nat := [360573359126560401, 360573433426828112, 360573490043982030, 360573546638878175, 360573571397643179, 360573571397700633, 360573583337433173, 360573608430890529, 360573631687835019, 360573665297869529]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360621311541952764, 360621311673932757⟩, ⟨(-242322389084497028), (-242321932104257088)⟩, true⟩

def words09 : List Nat := [360573679591251414, 360573693879026687, 360573713060842317, 360573751513599904, 360573779744050644, 360573807963434607, 360573816978763333, 360573816978820922, 360573797569532969, 360573806884263231]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk050
