import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk349A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk349A
