import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk254

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360629632646270937, 360629636471091705⟩, ⟨(-1171960900224464000), (-1171895180513062764)⟩, true⟩

def state01 : KState := ⟨⟨360594689639275946, 360594693467264102⟩, ⟨(-284657483284023097), (-284591683105686723)⟩, true⟩

def words00 : List Nat := [360583501717960419, 360583502328351294, 360583502348389944, 360583502368519087, 360583502368797260, 360583501994134556, 360583500077397675, 360583497363206764, 360583494649166228, 360583493920488860]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360497471161234318, 360497474992348756⟩, ⟨2186421181271303815, 2186487060904259545⟩, true⟩

def words01 : List Nat := [360583495905632945, 360583497890684105, 360583498980396292, 360583499113580411, 360583499113861114, 360583497807461153, 360583496501068416, 360583495153582913, 360583492815715243, 360583489432195502]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360557504974104663, 360557508808356389⟩, ⟨660078205602059122, 660144165000444634⟩, true⟩

def words02 : List Nat := [360583486048868568, 360583482893474814, 360583480759667078, 360583480168791027, 360583479577933109, 360583477714389311, 360583474311344962, 360583471904564492, 360583469497874794, 360583468075560497]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590481824191625, 360590485661614257⟩, ⟨(-178903291944419342), (-178837251894434138)⟩, true⟩

def words03 : List Nat := [360583467055089465, 360583464840353531, 360583462625725603, 360583461216424170, 360583460658382348, 360583459707757493, 360583458757171376, 360583456882707199, 360583455895044496, 360583456171739864]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360527229244023689, 360527233084577925⟩, ⟨1430305999701342486, 1430372119435408686⟩, true⟩

def words04 : List Nat := [360583456172010963, 360583456128988959, 360583454548049041, 360583451761556273, 360583448975233293, 360583445116113638, 360583442028599255, 360583440481247204, 360583438933981461, 360583436311274798]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360629443692923362, 360629447536624787⟩, ⟨(-1171511057999137070), (-1171444858153686152)⟩, true⟩

def words05 : List Nat := [360583434103252920, 360583432786149192, 360583431690989663, 360583432534404347, 360583432534711331, 360583432074179334, 360583432691760467, 360583434540280835, 360583436347821083, 360583438155290445]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360660531010780566, 360660534857655637⟩, ⟨(-1963533319342543714), (-1963467038680447032)⟩, true⟩

def words06 : List Nat := [360583438843425231, 360583438843758440, 360583440204441296, 360583441654015905, 360583442095855995, 360583443272809852, 360583443488109578, 360583443703427244, 360583445456460875, 360583448483399407]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597123569269415, 360597127419286492⟩, ⟨(-347991803628405428), (-347925442923783562)⟩, true⟩

def words07 : List Nat := [360583453047662951, 360583457611631607, 360583460980773012, 360583463397998339, 360583465406627917, 360583467415189690, 360583470493368085, 360583472038009710, 360583472574235501, 360583473110471148]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604630101880207, 360604633955040697⟩, ⟨(-539161847237718920), (-539095406423089554)⟩, true⟩

def words08 : List Nat := [360583474759961858, 360583477321920912, 360583480388963348, 360583483455828346, 360583485224565901, 360583485460378519, 360583485460654750, 360583484847881763, 360583484664526223, 360583485494547853]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360612742702405483, 360612746558742355⟩, ⟨(-746169742208729889), (-746103220412799749)⟩, true⟩

def words09 : List Nat := [360583485494845296, 360583485390733149, 360583485286567153, 360583485717807824, 360583486143838847, 360583486569890651, 360583486570190648, 360583486460816013, 360583487608540900, 360583488756287048]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk254
