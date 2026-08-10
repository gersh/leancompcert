import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk524A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360641908808247065, 360641926099414820⟩, ⟨(-3137367523599864024), (-3136755320732982074)⟩, true⟩

def state01 : KState := ⟨⟨360615291254132492, 360615308552218443⟩, ⟨(-1742537502676335755), (-1741924937261273865)⟩, true⟩

def words00 : List Nat := [360582066459714519, 360582067548368821, 360582068596761917, 360582069645329976, 360582070528959180, 360582071049489157, 360582071387014247, 360582071724599075, 360582072051920050, 360582072686898925]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360555884154952704, 360555901459874310⟩, ⟨1371380497531342919, 1371993421237960907⟩, true⟩

def words01 : List Nat := [360582073444321015, 360582074201851718, 360582074777103805, 360582075095920871, 360582075174971430, 360582075254232486, 360582075332871525, 360582075333597511, 360582075049256916, 360582074550702963]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572437064309136, 360572454376094509⟩, ⟨503535146238950611, 504148429777835923⟩, true⟩

def words02 : List Nat := [360582074052005306, 360582073558973243, 360582073249106211, 360582072929340501, 360582072609537370, 360582071975847345, 360582071287695719, 360582070876153531, 360582070464415083, 360582070024192504]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565785658729484, 360565802977425616⟩, ⟨852344930794556105, 852958576698615859⟩, true⟩

def words03 : List Nat := [360582069841443161, 360582069476719119, 360582069111869238, 360582069295208919, 360582069389634605, 360582069484175225, 360582069484837831, 360582069227756333, 360582068705855095, 360582068396508351]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576835260265973, 360576852585799666⟩, ⟨272852685972370822, 273466690473252578⟩, true⟩

def words04 : List Nat := [360582068098036192, 360582068098765996, 360582068006670685, 360582067732360260, 360582067457930875, 360582066966145600, 360582066657205227, 360582066645690850, 360582066634092738, 360582066440718127]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk524A
