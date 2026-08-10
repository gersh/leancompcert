import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk765A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk765B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk765A

def state06 : KState := ⟨⟨362486266019948904, 362486353616170423⟩, ⟨(-92148184726087789), (-87619396681548857)⟩, true⟩

def words05 : List Nat := [371285208298686768, 371285208377332256, 371285208586884601, 371285208712862502, 371285208875206366, 371285209038532600, 371285209195503973, 371285209198142621, 371285209158860319, 371285209177139043]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486071326374871, 362486158946078423⟩, ⟨(-77237986918212355), (-72707400966977015)⟩, true⟩

def words06 : List Nat := [371285209364347262, 371285209366985812, 371285209327105922, 371285209283280598, 371285209243883312, 371285209246841452, 371285209255909275, 371285209322732658, 371285209388657018, 371285209403810894]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497046167158825, 362497133810711485⟩, ⟨(-917673886589368581), (-913141474389257143)⟩, true⟩

def words07 : List Nat := [371285209506221711, 371285209609989387, 371285209783444108, 371285209786083249, 371285209732555713, 371285209652373379, 371285209641675390, 371285209644583471, 371285209787422544, 371285209946118581]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477399149446504, 362477486816818082⟩, ⟨586976280759068907, 591510517131114293⟩, true⟩

def words08 : List Nat := [371285210088673403, 371285210091833894, 371285210178952370, 371285210267451141, 371285210364580327, 371285210367219849, 371285210252499376, 371285210104261750, 371285209954981914, 371285209894467007]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475778260252903, 362475865951400932⟩, ⟨711183946570676720, 715720004104294284⟩, true⟩

def words09 : List Nat := [371285209851324588, 371285209910125127, 371285209934501655, 371285209937187275, 371285209819670105, 371285209755514198, 371285209793005708, 371285209795645496, 371285209673574989, 371285209554587673]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk765B
