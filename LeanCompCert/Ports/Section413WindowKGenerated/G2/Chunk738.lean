import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk738

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575346730353639, 360575381980997829⟩, ⟨516529629597504288, 518286772376642460⟩, true⟩

def state01 : KState := ⟨⟨360557145029556156, 360557180290091957⟩, ⟨1859790659469903144, 1861548532300007128⟩, true⟩

def words00 : List Nat := [360582404742700008, 360582404571492759, 360582404216766304, 360582403758503319, 360582403300082564, 360582402758954519, 360582402310087173, 360582401946677738, 360582401583154591, 360582401107492039]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596631869168104, 360596667139605189⟩, ⟨(-1054968914992613686), (-1053210311299877482)⟩, true⟩

def words01 : List Nat := [360582400766646645, 360582400537489298, 360582400308030347, 360582400221080464, 360582400176452468, 360582399959033204, 360582399741419030, 360582399668437040, 360582399862559572, 360582400056914629]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584540390505110, 360584575670948459⟩, ⟨(-162350812045959123), (-160591469640745701)⟩, true⟩

def words02 : List Nat := [360582400110807663, 360582400170429168, 360582400413026067, 360582400655924351, 360582400852168404, 360582400865284205, 360582400866232899, 360582400763090805, 360582400659765672, 360582400548443810]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561781764001747, 360561817054336447⟩, ⟨1518069295723595219, 1519829368456229815⟩, true⟩

def words03 : List Nat := [360582400564664599, 360582400581090342, 360582400582025917, 360582400506942693, 360582400443098068, 360582400333276265, 360582400237150810, 360582400238200766, 360582400069921842, 360582399792262453]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581071872295372, 360581107172551656⟩, ⟨93515059182181406, 95275864573140124⟩, true⟩

def words04 : List Nat := [360582399514367819, 360582399346318815, 360582399281660263, 360582399113240587, 360582398944753979, 360582398615819183, 360582398103468461, 360582397774519810, 360582397445268877, 360582397299356980]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360564386822204736, 360564422132458228⟩, ⟨1325764374448472467, 1327525918182912699⟩, true⟩

def words05 : List Nat := [360582397282823485, 360582397159745885, 360582397036477212, 360582396839785313, 360582396785856938, 360582396685856580, 360582396585760931, 360582396343587672, 360582395918045734, 360582395675894228]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562369087486725, 360562404407627534⟩, ⟨1474754673277300486, 1476516947338754788⟩, true⟩

def words06 : List Nat := [360582395433400629, 360582395342446969, 360582395068226711, 360582394683417212, 360582394298437213, 360582393744607573, 360582393307297396, 360582393053187382, 360582392798969719, 360582392453482939]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575702615333013, 360575737945408562⟩, ⟨489661325870143787, 491424333859025399⟩, true⟩

def words07 : List Nat := [360582392183766870, 360582391872632200, 360582391561183976, 360582391361268388, 360582391047547001, 360582390581934187, 360582390116124189, 360582389833593335, 360582389690200992, 360582389601253974]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570713122937134, 360570748463017329⟩, ⟨858259635024809111, 860023382206425093⟩, true⟩

def words08 : List Nat := [360582389512166836, 360582389330562437, 360582389204310254, 360582389233373294, 360582389234267974, 360582389137314084, 360582388857178702, 360582388437244882, 360582388017121779, 360582387702186452]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551990870169913, 360552026220164167⟩, ⟨2241765691388376869, 2243530171168712091⟩, true⟩

def words09 : List Nat := [360582387545518809, 360582387469854107, 360582387394052451, 360582387226990160, 360582386876714850, 360582386480557644, 360582386084102916, 360582385870701311, 360582385630855732, 360582385221127208]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk738
