import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk111

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360519738786713589, 360519739463926685⟩, ⟨724365910572822987, 724371004826079449⟩, true⟩

def state01 : KState := ⟨⟨360607769637409121, 360607770315898236⟩, ⟨(-253229599698901020), (-253224491275451916)⟩, true⟩

def words00 : List Nat := [360584992234492014, 360584989705838615, 360584989705959174, 360584986394791801, 360584983084198871, 360584977647607125, 360584979057085689, 360584981762058827, 360584981762181631, 360584979883779125]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360822956956057902, 360822957635823739⟩, ⟨(-2645479001403563152), (-2645473878789398474)⟩, true⟩

def words01 : List Nat := [360584986223322779, 360584992561764646, 360585006948803083, 360585013315854668, 360585013315981356, 360585013048100514, 360585020557758530, 360585033912326465, 360585055308454459, 360585076700764896]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360661684663764091, 360661685344821649⟩, ⟨(-852216569182306356), (-852211432197919082)⟩, true⟩

def words02 : List Nat := [360585091798529162, 360585102341108209, 360585112058842207, 360585121774868033, 360585128660405503, 360585128660540981, 360585127542590767, 360585122366271387, 360585117190856029, 360585123361873314]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360429780426344471, 360429781108678230⟩, ⟨1730830980850224416, 1730836132045231458⟩, true⟩

def words03 : List Nat := [360585138266256874, 360585153167989761, 360585163985720690, 360585171596999691, 360585174046271573, 360585176495139055, 360585176495250880, 360585175411089197, 360585166343482253, 360585152395217300]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360520477030571391, 360520477714186166⟩, ⟨719747977852319813, 719753143324392199⟩, true⟩

def words04 : List Nat := [360585138449426437, 360585126680114078, 360585118998574813, 360585112384824852, 360585105772248849, 360585092339966662, 360585070935009864, 360585054474812386, 360585038017528350, 360585029565605394]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360548320269752316, 360548320954664767⟩, ⟨408726129530851197, 408731309478226497⟩, true⟩

def words05 : List Nat := [360585023776845212, 360585011357241214, 360584998939838413, 360584989697800235, 360584987091529155, 360584979466718623, 360584971843260173, 360584960178052256, 360584948905891255, 360584945623972852]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360435968156107870, 360435968842300462⟩, ⟨1663171599593886092, 1663176793834197224⟩, true⟩

def words06 : List Nat := [360584947048450744, 360584947048586729, 360584943801140771, 360584935892518086, 360584927985292847, 360584912081871058, 360584900258108606, 360584890618735134, 360584880981074401, 360584865600924831]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360635434689382204, 360635435376862263⟩, ⟨(-565709464012354451), (-565704255384938135)⟩, true⟩

def words07 : List Nat := [360584852272169442, 360584846917480221, 360584844181000374, 360584844181136585, 360584843052875332, 360584834839457048, 360584826627481776, 360584831185233242, 360584835711659514, 360584840237305432]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360645055311090365, 360645055999866397⟩, ⟨(-674169211416883394), (-674163988293997372)⟩, true⟩

def words08 : List Nat := [360584840740879423, 360584840741015624, 360584833324766204, 360584830854715902, 360584828385071647, 360584823817181751, 360584823374517037, 360584816935221584, 360584810497051324, 360584814378179864]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360549328776400506, 360549329466463182⟩, ⟨397384838172686510, 397390075699691402⟩, true⟩

def words09 : List Nat := [360584821085470456, 360584827791588167, 360584827791712346, 360584827455744412, 360584823438354538, 360584817335747488, 360584813064225541, 360584813891209037, 360584813891330674, 360584810723222084]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk111
