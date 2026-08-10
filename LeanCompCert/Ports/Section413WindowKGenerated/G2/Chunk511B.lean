import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk511A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk511B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk511A

def state06 : KState := ⟨⟨360569252474977195, 360569268925352603⟩, ⟨649652152956939589, 650220817415163795⟩, true⟩

def words05 : List Nat := [360581977047283687, 360581977878596185, 360581978416419907, 360581978573171337, 360581978573766091, 360581978517081206, 360581978783837171, 360581978784544527, 360581978727732611, 360581978480032337]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592055231296723, 360592071688358660⟩, ⟨(-517180270929714345), (-516611264355943405)⟩, true⟩

def words06 : List Nat := [360581978232185420, 360581978045531078, 360581978046112945, 360581978040057222, 360581978033953237, 360581977697457125, 360581976979854661, 360581976429316017, 360581975878587573, 360581975906287645]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571090962614461, 360571107426407430⟩, ⟨555688325310108147, 556257676344768347⟩, true⟩

def words07 : List Nat := [360581975906918217, 360581975859384609, 360581976045096233, 360581976468949003, 360581976666134361, 360581976863425888, 360581976864067093, 360581976768145002, 360581976291274878, 360581976079716238]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360543622940059439, 360543639410515286⟩, ⟨1961552356269960691, 1962122048344148215⟩, true⟩

def words08 : List Nat := [360581975867934392, 360581975624968925, 360581975111330928, 360581974294748197, 360581973478070281, 360581972479332391, 360581971712590737, 360581971075503134, 360581970438363078, 360581969593135801]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602892297007605, 360602908774156045⟩, ⟨(-1072884487521140891), (-1072314452820233063)⟩, true⟩

def words09 : List Nat := [360581968844950144, 360581967990097310, 360581967135062345, 360581966660821545, 360581966319012344, 360581965650348488, 360581964981575205, 360581964722129803, 360581965131765724, 360581965541546912]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk511B
