import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk628

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362459249636715809, 362459307670670825⟩, ⟨1636316999308531067, 1638778691013105139⟩, true⟩

def state01 : KState := ⟨⟨362479930881934873, 362479988934971906⟩, ⟨337455511062468940, 339918401216652100⟩, true⟩

def words00 : List Nat := [371285402458681543, 371285402299110190, 371285402013631332, 371285401895942961, 371285401777574376, 371285401626043718, 371285401189156533, 371285400981450114, 371285400784384530, 371285400786607262]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487440218317904, 362487498290808452⟩, ⟨(-134264271439737358), (-131800159312871188)⟩, true⟩

def words01 : List Nat := [371285400702083890, 371285400565137102, 371285400470427849, 371285400472785479, 371285400441781377, 371285400432723279, 371285400422904078, 371285400412841237, 371285400227686815, 371285400263726539]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475890495561081, 362475948587020579⟩, ⟨591338240358660483, 593803544214505557⟩, true⟩

def words02 : List Nat := [371285400428166023, 371285400430299435, 371285400282145454, 371285400128624608, 371285399974300739, 371285399828743113, 371285399567256912, 371285399559962822, 371285399551992010, 371285399542682119]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489223620436943, 362489281731243102⟩, ⟨(-246411726579739722), (-243945207080986806)⟩, true⟩

def words03 : List Nat := [371285399472196191, 371285399553330429, 371285399816946611, 371285399819080555, 371285399776056693, 371285399674311317, 371285399678370253, 371285399680743618, 371285399723621586, 371285399787813160]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478132408465536, 362478190538516253⟩, ⟨450570237207629263, 453037966134121245⟩, true⟩

def words04 : List Nat := [371285399850410770, 371285399852555013, 371285399673169868, 371285399577205363, 371285399480212207, 371285399460867951, 371285399249212437, 371285399039625493, 371285398829150355, 371285398779823081]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk628
