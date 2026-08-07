import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk137

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603114740042374, 360603115792211801⟩, ⟨(-293785176674755626), (-293775414454752320)⟩, true⟩

def state01 : KState := ⟨⟨360761188850423180, 360761189904211327⟩, ⟨(-2460734336700044513), (-2460724552295476307)⟩, true⟩

def words00 : List Nat := [360581673896556110, 360581673557147053, 360581677767087553, 360581681976463012, 360581684839858702, 360581690829350206, 360581694116629716, 360581697403447015, 360581705983354412, 360581719074053390]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360552183629961051, 360552184685354606⟩, ⟨406237253920076712, 406247060342755470⟩, true⟩

def words01 : List Nat := [360581737455621099, 360581755834540266, 360581770143265214, 360581779168621892, 360581785105784326, 360581791042127042, 360581795059530857, 360581796687380861, 360581796687533037, 360581794529402912]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360660775124841139, 360660776181841518⟩, ⟨(-1083892793292997025), (-1083882964816588385)⟩, true⟩

def words02 : List Nat := [360581795502083712, 360581801325633959, 360581812435736281, 360581823544252087, 360581829948913755, 360581831080198441, 360581831080338858, 360581830126739488, 360581833503965647, 360581839253371881]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565145232282672, 360565146290906095⟩, ⟨229808795851108186, 229818646619922960⟩, true⟩

def words03 : List Nat := [360581841718332229, 360581844182951944, 360581849671503788, 360581859203642526, 360581865802729588, 360581872400883957, 360581875710395361, 360581875710565923, 360581873756074885, 360581872538840588]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360504835055452632, 360504836115684950⟩, ⟨1058124684137586146, 1058134557020610614⟩, true⟩

def words04 : List Nat := [360581871321730630, 360581867661020014, 360581858738840045, 360581847129497860, 360581835521817269, 360581822569543211, 360581813030139056, 360581806692656630, 360581800356074731, 360581791356195540]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360717643545823004, 360717644607666551⟩, ⟨(-1869260257800460488), (-1869250362754855430)⟩, true⟩

def words05 : List Nat := [360581785759996111, 360581785431701954, 360581786406812220, 360581788159687711, 360581788159847778, 360581784831415561, 360581783437872539, 360581788050715319, 360581797924150055, 360581807796188108]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360666145380666854, 360666146444141694⟩, ⟨(-1160623614375310472), (-1160613696875278992)⟩, true⟩

def words06 : List Nat := [360581813629295942, 360581819698812119, 360581831026432564, 360581842352456935, 360581852339856406, 360581857082034455, 360581858407061685, 360581859731914341, 360581860772421505, 360581866893137753]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360530358080168132, 360530359145253970⟩, ⟨710182996908731831, 710192936600243653⟩, true⟩

def words07 : List Nat := [360581876399708790, 360581885904932878, 360581892756473274, 360581896818625496, 360581897766512178, 360581898714308762, 360581901900120292, 360581901900291362, 360581900834357056, 360581897094208995]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360638428528040219, 360638429594742740⟩, ⟨(-779787493221751216), (-779777531244099568)⟩, true⟩

def words08 : List Nat := [360581894859225540, 360581899027477666, 360581900329434411, 360581901631231509, 360581901631389294, 360581898418850187, 360581892026924140, 360581887271212446, 360581883000563898, 360581887100997247]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589146452704833, 360589147521038061⟩, ⟨(-99947301077828925), (-99937316604758859)⟩, true⟩

def words09 : List Nat := [360581888553597486, 360581890006005691, 360581892932871265, 360581900118428956, 360581904738326691, 360581909357582413, 360581909868509541, 360581909868680861, 360581905686306133, 360581906211234079]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk137
