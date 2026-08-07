import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk138

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589146452704833, 360589147521038061⟩, ⟨(-99947301077828925), (-99937316604758859)⟩, true⟩

def state01 : KState := ⟨⟨360599542179509100, 360599543249456867⟩, ⟨(-243662747189760270), (-243652740428049220)⟩, true⟩

def words00 : List Nat := [360581909523097020, 360581909894074523, 360581909894227394, 360581907066819730, 360581904239791435, 360581897833833997, 360581897643765217, 360581900161934374, 360581900162087275, 360581901316184255]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360608307438694278, 360608308510263453⟩, ⟨(-365108357478401744), (-365098328317018698)⟩, true⟩

def words01 : List Nat := [360581902383100439, 360581903449909521, 360581906677257826, 360581906677429378, 360581904699619112, 360581898225626785, 360581891752538014, 360581888484740654, 360581890396604320, 360581892308229084]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360505503150888993, 360505504224091940⟩, ⟨1055355779526472532, 1055365831274918218⟩, true⟩

def words02 : List Nat := [360581892308382527, 360581890509355254, 360581883510352101, 360581878752889855, 360581873996071611, 360581865491172270, 360581854378212464, 360581839220042250, 360581824064031753, 360581814117893453]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360468087511786177, 360468088586609767⟩, ⟨1573138796429288818, 1573148870599377716⟩, true⟩

def words03 : List Nat := [360581808600724154, 360581808291263371, 360581807981826301, 360581804235497091, 360581795297498892, 360581785038204313, 360581774780342887, 360581767864184300, 360581763625856797, 360581755412520127]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360672745937976673, 360672747014423316⟩, ⟨(-1260121385653851326), (-1260111289012598174)⟩, true⟩

def words04 : List Nat := [360581747200331850, 360581744188613817, 360581747120453105, 360581750410337385, 360581750410496686, 360581750345513152, 360581754741977627, 360581759137857029, 360581764249695545, 360581770818552073]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360644091515033224, 360644092593123688⟩, ⟨(-863454918378762674), (-863444798962838588)⟩, true⟩

def words05 : List Nat := [360581774245970935, 360581777672911751, 360581780894494068, 360581786754170539, 360581789270798741, 360581791787091240, 360581791787244897, 360581791182502595, 360581794988378692, 360581799483033303]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605686307284919, 360605687386995570⟩, ⟨(-330958260183569812), (-330948118303517934)⟩, true⟩

def words06 : List Nat := [360581807525397518, 360581813166583523, 360581816188582911, 360581819210165037, 360581819482160452, 360581822382527690, 360581825037380363, 360581827691880475, 360581827692035778, 360581828392092282]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360763244555441381, 360763245636779425⟩, ⟨(-2517602511144253100), (-2517592346684189842)⟩, true⟩

def words07 : List Nat := [360581828392233533, 360581827846459901, 360581831929499926, 360581836791612670, 360581836791771904, 360581836782166390, 360581841935112150, 360581849833688538, 360581862902690161, 360581875969847346]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360716591235310049, 360716592318293239⟩, ⟨(-1870034918131232057), (-1870024730828244285)⟩, true⟩

def words08 : List Nat := [360581885097419127, 360581893569489139, 360581907210177812, 360581920848952516, 360581933170293396, 360581942531293000, 360581949255102719, 360581955977964509, 360581961307958110, 360581971000113969]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360481030776168069, 360481031860776924⟩, ⟨1403394556387672525, 1403404766279558235⟩, true⟩

def words09 : List Nat := [360581983351553268, 360581995701247343, 360582004066784867, 360582007285420674, 360582007285567817, 360582006891401280, 360582007568865442, 360582007569038170, 360582003496419308, 360581996232451713]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk138
