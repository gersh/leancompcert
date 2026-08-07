import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk524

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362517160764938668, 362517200590125443⟩, ⟨(-1685508662164953752), (-1684098859369333586)⟩, true⟩

def state01 : KState := ⟨⟨362494751597538302, 362494791438569533⟩, ⟨(-511158535342548431), (-509747902214323265)⟩, true⟩

def words00 : List Nat := [371285062527107732, 371285062914107423, 371285063458964005, 371285064004696391, 371285064616373818, 371285064743536060, 371285064872039558, 371285065001131807, 371285065279303371, 371285065466880111]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467872658564566, 362467912515402149⟩, ⟨897788254669304656, 899199716285334800⟩, true⟩

def words01 : List Nat := [371285065884249280, 371285066302296658, 371285066720066223, 371285066721822195, 371285066710251635, 371285066712235073, 371285066894162835, 371285066895918718, 371285066593385100, 371285066268097406]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474468803916339, 362474508676486842⟩, ⟨551999768087424525, 553412054503863039⟩, true⟩

def words02 : List Nat := [371285065942062205, 371285065818260464, 371285065511967961, 371285065356183745, 371285065199858548, 371285064978994296, 371285064432265483, 371285064209493686, 371285063985841463, 371285063932151612]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473919558376704, 362473959446954614⟩, ⟨580853857758618764, 582266983522028760⟩, true⟩

def words03 : List Nat := [371285063732147980, 371285063533032161, 371285063495516396, 371285063497471322, 371285063576451019, 371285063673049944, 371285063674395386, 371285063630823932, 371285063145885476, 371285062936342906]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470978360933296, 362471018265160927⟩, ⟨735153992507021310, 736567939023596768⟩, true⟩

def words04 : List Nat := [371285062850275925, 371285062852040932, 371285062630009661, 371285062407743541, 371285062184800649, 371285061991347495, 371285061615515595, 371285061578894630, 371285061541645227, 371285061505180443]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486165625928616, 362486205546035659⟩, ⟨(-61502888021277022), (-60088108550098338)⟩, true⟩

def words05 : List Nat := [371285061238653705, 371285061070184243, 371285061093336728, 371285061095093699, 371285060804867237, 371285060484060019, 371285060202859671, 371285060204829271, 371285060135984819, 371285060159776341]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470893259010764, 362470933194988653⟩, ⟨739687502173334981, 741103114309332267⟩, true⟩

def words06 : List Nat := [371285060161105400, 371285060136301282, 371285059739678971, 371285059602096347, 371285059463649413, 371285059342983825, 371285058807023075, 371285058271999798, 371285057736290040, 371285057515825500]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362458506005779104, 362458545957607629⟩, ⟨1389800296693840383, 1391216740593248607⟩, true⟩

def words07 : List Nat := [371285057301156518, 371285057356431723, 371285057411472557, 371285057413230283, 371285056984469134, 371285056665024685, 371285056344701907, 371285056323610817, 371285055926082459, 371285055422939056]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481784741689949, 362481824709249010⟩, ⟨167987032009590388, 169404301527997528⟩, true⟩

def words08 : List Nat := [371285054919020918, 371285054517238520, 371285053933233073, 371285053654621665, 371285053375490431, 371285053036262538, 371285052460796133, 371285052210954612, 371285052070763834, 371285052072585417]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478605349818200, 362478645333410188⟩, ⟨334909413791392113, 336327524958541073⟩, true⟩

def words09 : List Nat := [371285052012416345, 371285051953250088, 371285051981806715, 371285051983753486, 371285052001804625, 371285052067872304, 371285052120656881, 371285052122415550, 371285051691809215, 371285051571980827]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk524
