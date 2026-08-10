import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk192A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574793570112034, 360574795702051713⟩, ⟨183043721785884235, 183071426025961653⟩, true⟩

def state01 : KState := ⟨⟨360529760700514599, 360529762834769257⟩, ⟨1047411247210216647, 1047438995909325741⟩, true⟩

def words00 : List Nat := [360584330175772936, 360584328478761321, 360584324081287025, 360584317892239020, 360584311703795917, 360584303978099883, 360584298529044954, 360584295773464071, 360584293018139536, 360584288550329347]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360655193664637574, 360655195801208141⟩, ⟨(-1362788839270286507), (-1362761046070841937)⟩, true⟩

def words01 : List Nat := [360584285712273171, 360584285566800827, 360584287967498324, 360584289786306009, 360584289786538240, 360584288998328237, 360584288210154749, 360584288831294052, 360584292520721239, 360584296209820033]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571880669729210, 360571882808643680⟩, ⟨238848999839718266, 238876838100330726⟩, true⟩

def words02 : List Nat := [360584298173175600, 360584300250973679, 360584304073860025, 360584307896422886, 360584310991549663, 360584311392953221, 360584311393173920, 360584309618526255, 360584307844017358, 360584304901108596]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360514717349452108, 360514719490680930⟩, ⟨1338723710205756607, 1338751592983073121⟩, true⟩

def words03 : List Nat := [360584306296687204, 360584308338041496, 360584309012262449, 360584309012508424, 360584308178255436, 360584306661081373, 360584306312420625, 360584306312666585, 360584304790751796, 360584301174307909]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598453259157703, 360598455402710952⟩, ⟨(-272995592314779504), (-272967664804027958)⟩, true⟩

def words04 : List Nat := [360584297558183327, 360584295735643056, 360584295262076176, 360584294723340245, 360584294184640387, 360584291332082441, 360584285791003789, 360584281387703131, 360584276984788366, 360584276000871878]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk192A
