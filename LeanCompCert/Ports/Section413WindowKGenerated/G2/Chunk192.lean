import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk192

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

def state06 : KState := ⟨⟨360550749103078977, 360550751248974719⟩, ⟨645495820100042085, 645523792715493247⟩, true⟩

def words05 : List Nat := [360584276001093739, 360584274941931854, 360584273882834022, 360584274652927404, 360584275043800547, 360584275434673408, 360584275434896424, 360584273700882822, 360584269281441124, 360584267541431391]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360528752542165780, 360528754690379497⟩, ⟨1068787808158150834, 1068815825429553368⟩, true⟩

def words06 : List Nat := [360584265801520723, 360584262942662658, 360584257399068861, 360584250513983250, 360584243629568138, 360584236066877418, 360584230372335653, 360584227355174176, 360584224338300977, 360584219964143356]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602598047884868, 360602600198427566⟩, ⟨(-354761937159912717), (-354733874997951069)⟩, true⟩

def words07 : List Nat := [360584217086172957, 360584214146682802, 360584211207424222, 360584210943628935, 360584209571427370, 360584205885736934, 360584202200381977, 360584200183708279, 360584201138266182, 360584202092779625]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360530607995129102, 360530610148015027⟩, ⟨1033073138005724558, 1033101245357070042⟩, true⟩

def words08 : List Nat := [360584202092999093, 360584201708357010, 360584199866292088, 360584198434816637, 360584197003428961, 360584193314018128, 360584186946706727, 360584179226862232, 360584171507771207, 360584166459334730]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360425216313864134, 360425218469076148⟩, ⟨3066946873648573609, 3066975025881844451⟩, true⟩

def words09 : List Nat := [360584163683301270, 360584162722833642, 360584161762433357, 360584159174474150, 360584156244173100, 360584151581950731, 360584146920137612, 360584143460593180, 360584137326060988, 360584129092178835]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk192
