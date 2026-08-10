import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk628A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk628B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk628A

def state06 : KState := ⟨⟨362472649584278936, 362472707733557814⟩, ⟨795266095443895183, 797735032958318595⟩, true⟩

def words05 : List Nat := [371285398805019679, 371285398945753508, 371285399019687791, 371285399021836607, 371285398868904825, 371285398762705965, 371285398772899157, 371285398775034227, 371285398595342193, 371285398395870228]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486255032358352, 362486313200728088⟩, ⟨(-59988216947322720), (-57518079283122908)⟩, true⟩

def words06 : List Nat := [371285398246613065, 371285398248965315, 371285398299194704, 371285398425198066, 371285398476902303, 371285398479043749, 371285398300088650, 371285398225371419, 371285398325299238, 371285398342060609]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495499755949659, 362495557943790531⟩, ⟨(-641223350931889023), (-638751989020098583)⟩, true⟩

def words07 : List Nat := [371285398354945094, 371285398368567592, 371285398634283470, 371285398811217504, 371285399063400309, 371285399316387048, 371285399567792821, 371285399569927949, 371285399671568522, 371285399835792566]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478719196695947, 362478777403570855⟩, ⟨414011315624496692, 416483874495860610⟩, true⟩

def words08 : List Nat := [371285400063597464, 371285400065735739, 371285400020724896, 371285399942968200, 371285399864415413, 371285399863526780, 371285399776017812, 371285399798534832, 371285399819458562, 371285399821673827]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362513598431530282, 362513656657691490⟩, ⟨(-1779716905434758846), (-1777243133550540298)⟩, true⟩

def words09 : List Nat := [371285399827253905, 371285399939237223, 371285400277620761, 371285400422781850, 371285400499398883, 371285400576677653, 371285400905805231, 371285401146871435, 371285401597534728, 371285402049123256]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk628B
