import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk349

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570641264090817, 360570648683412763⟩, ⟨392153249641069112, 392328308358492748⟩, true⟩

def state01 : KState := ⟨⟨360579707731811139, 360579715155557296⟩, ⟨75718499827903038, 75893712972313076⟩, true⟩

def words00 : List Nat := [360581889860502277, 360581890383944555, 360581890730734326, 360581891077590509, 360581891078023918, 360581890726929102, 360581889914329860, 360581889663373074, 360581889412300210, 360581889137596034]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360630890722304718, 360630898150513706⟩, ⟨(-1711420894818757891), (-1711245525855526737)⟩, true⟩

def words01 : List Nat := [360581889075745202, 360581888588060472, 360581888431639556, 360581889446612456, 360581890255491576, 360581891064409458, 360581891421363254, 360581892006068413, 360581893409830380, 360581894813671820]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360635895196815215, 360635902629437704⟩, ⟨(-1886300305955158944), (-1886124782850112908)⟩, true⟩

def words02 : List Nat := [360581896763682405, 360581898371907423, 360581899354242045, 360581900336564495, 360581900758346319, 360581901591284219, 360581902982473126, 360581904373672284, 360581905354886548, 360581906901206331]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360639795691769125, 360639803128811904⟩, ⟨(-2022646027637911001), (-2022470350110278901)⟩, true⟩

def words03 : List Nat := [360581908683880526, 360581910466588312, 360581912892471161, 360581914501928011, 360581915304724854, 360581916107514515, 360581916535028857, 360581917374202689, 360581919031300392, 360581920688409218]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612891151750996, 360612898593255158⟩, ⟨(-1082754717758077999), (-1082578884327086567)⟩, true⟩

def words04 : List Nat := [360581921842173638, 360581922179825617, 360581923120978151, 360581924062225236, 360581924612858633, 360581924613327398, 360581924612450551, 360581923974992856, 360581923517346254, 360581924404123887]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360566488817000930, 360566496262926311⟩, ⟨539175944294628885, 539351932269435533⟩, true⟩

def words05 : List Nat := [360581925267363368, 360581926130637875, 360581926500444881, 360581926500913689, 360581926055136215, 360581925404423384, 360581924753607660, 360581924390179405, 360581924390597224, 360581923949776124]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609737322358395, 360609744772707540⟩, ⟨(-972856150619359970), (-972680007968380908)⟩, true⟩

def words06 : List Nat := [360581923884763452, 360581924671330510, 360581926274817113, 360581927878301743, 360581928658906369, 360581928659375324, 360581929186241849, 360581929748174811, 360581930073679300, 360581930869531527]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567904840634551, 360567912295453673⟩, ⟨490389471032063225, 490565770019926253⟩, true⟩

def words07 : List Nat := [360581931253221005, 360581931636947905, 360581932487152457, 360581933898494470, 360581935083939746, 360581936269393362, 360581936979099890, 360581936979568980, 360581936874520903, 360581936474127771]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575730414554598, 360575737873787715⟩, ⟨216560434050154814, 216736887461780450⟩, true⟩

def words08 : List Nat := [360581936488967421, 360581936489436576, 360581936090615799, 360581935092298095, 360581934093960928, 360581932891051852, 360581932466563176, 360581932514556056, 360581932514974056, 360581932126072991]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581871448873932, 360581878912542731⟩, ⟨1477627758262614, 1654236396138234⟩, true⟩

def words09 : List Nat := [360581931949430856, 360581931891182909, 360581931832802293, 360581931751295149, 360581930855708870, 360581929261904558, 360581927668099440, 360581926669247935, 360581926177295558, 360581926176439764]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk349
