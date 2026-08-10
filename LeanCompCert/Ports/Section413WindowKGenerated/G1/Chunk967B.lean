import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk967A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk967B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk967A

def state06 : KState := ⟨⟨362490439098561058, 362490581565376626⟩, ⟨(-519615741962527772), (-510308660600035234)⟩, true⟩

def words05 : List Nat := [371285306746542656, 371285306901439633, 371285307054753938, 371285307120195459, 371285307204454573, 371285307290381345, 371285307481499898, 371285307541443181, 371285307598521889, 371285307656874234]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490137734009011, 362490280231261284⟩, ⟨(-490443742743386520), (-481133716176314206)⟩, true⟩

def words06 : List Nat := [371285307739672440, 371285307770666866, 371285307907159893, 371285308045012096, 371285308165606678, 371285308169001069, 371285308159179013, 371285308175703443, 371285308297229615, 371285308352122118]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494429494029547, 362494572022127638⟩, ⟨(-905793803009332773), (-896480791331650219)⟩, true⟩

def words07 : List Nat := [371285308405638749, 371285308460288625, 371285308573333554, 371285308637605840, 371285308707369829, 371285308778418707, 371285308848662443, 371285308852081520, 371285308938900343, 371285309038780374]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492012798529592, 362492155356913762⟩, ⟨(-671861797457038568), (-662545854535261488)⟩, true⟩

def words08 : List Nat := [371285309204056485, 371285309296367893, 371285309387362141, 371285309479552445, 371285309590774392, 371285309664179108, 371285309842990272, 371285310023150092, 371285310164282787, 371285310238519126]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362511940268517584, 362512082857642300⟩, ⟨(-2600757558157858888), (-2591438639709848176)⟩, true⟩

def words09 : List Nat := [371285310406960553, 371285310577193425, 371285310833277095, 371285310948123465, 371285311043251738, 371285311139441961, 371285311341079473, 371285311514553159, 371285311793418708, 371285312073872403]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk967B
