import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk212A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk212B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk212A

def state06 : KState := ⟨⟨360623797365118167, 360623800002805891⟩, ⟨(-918385275343249802), (-918347330308504574)⟩, true⟩

def words05 : List Nat := [360580591500360222, 360580593849186958, 360580597659640795, 360580599264801253, 360580599265054756, 360580599080894313, 360580599862264106, 360580601952985770, 360580603985104410, 360580606017089862]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606048092208082, 360606050732503648⟩, ⟨(-541523053971534111), (-541485053481088393)⟩, true⟩

def words06 : List Nat := [360580606656499580, 360580606656773587, 360580605092357492, 360580603848229541, 360580602604146468, 360580600808483279, 360580599484038859, 360580596603910559, 360580593723999574, 360580594239932491]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360534220562661492, 360534223205541677⟩, ⟨986826483939682787, 986864539417867313⟩, true⟩

def words07 : List Nat := [360580596974702756, 360580599709268210, 360580600719815349, 360580601449012693, 360580601449242906, 360580600688019854, 360580601362543815, 360580601362817995, 360580600597959879, 360580598418860186]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589852516310260, 360589855161776927⟩, ⟨(-197238027204143423), (-197199916672594805)⟩, true⟩

def words08 : List Nat := [360580596239899200, 360580594715990054, 360580596096932673, 360580597885454289, 360580597885711085, 360580597438658892, 360580595911614024, 360580594326837379, 360580592742129732, 360580593036152363]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584103667229535, 360584106315309487⟩, ⟨(-74740352587977359), (-74702186407148533)⟩, true⟩

def words09 : List Nat := [360580593036396849, 360580592133294566, 360580592000618723, 360580594559381702, 360580596569408736, 360580598579293497, 360580599275016829, 360580599275291674, 360580599170094855, 360580599335054704]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk212B
